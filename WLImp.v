Require Export SfLib.

(** WLImp only has wakelock related statements and control flow statements *)

(** Android Wakelocks *)
Inductive wakelock : Type :=
  WakeLock : nat -> wakelock.

Definition WL0 : wakelock := WakeLock 0.
Definition WL1 : wakelock := WakeLock 1.

Theorem eq_wl_dec : forall wl1 wl2 : wakelock, {wl1 = wl2} + {wl1 <> wl2}.
Proof.
   intros wl1 wl2.
   destruct wl1 as [n1]. destruct wl2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   Case "n1 = n2".
     left. rewrite Heq. reflexivity.
   Case "n1 <> n2".
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined.

(** A wlstate represents the current state of _all_ the wakelocks at
    some point in the execution of a program. We just hold list of all
    the wakelocks that are active. A lock can be held multiple times*)
Definition wlstate : Type := list wakelock.

Definition empty_wlstate : wlstate :=  [].

Definition isAnyWlHeld (st : wlstate ): bool := 
  match st with 
  | [] => false
  | cons _ _ => true
  end.

Fixpoint beq_wl (wl wl': wakelock) : bool :=
  match (wl, wl') with
  | (WakeLock n, WakeLock n') => beq_nat n n'
  end.

Fixpoint isWlHeld (wl: wakelock) (st: wlstate) : bool := 
  match st with 
  | [] => false
  | cons wl' st' => if ( beq_wl wl wl' ) then true
                        else isWlHeld wl st'
  end.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BIsHeld : wakelock -> bexp.

Fixpoint beval (st : wlstate) (b : bexp)  : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  | BIsHeld wl  => (isWlHeld wl st)
  end.


Inductive com : Type :=
  | CSkip : com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAcq : wakelock -> com                   (** Acquire wakelock *)
  | CRel : wakelock -> com.                   (** Release wakelock *)


Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" 
  | Case_aux c "Acq" | Case_aux c "Rel" ].

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'ACQ' l" :=
  (CAcq l) (at level 80, right associativity).
Notation "'REL' l" :=
  (CRel l) (at level 80, right associativity).


(** A process is just a (command, wlstate) tuple. Command is current
command that needs to be executed and wlstate is state of all locks *)
Inductive process : Type :=
  Process : com -> wlstate -> process.

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> wlstate -> wlstate -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ;; c2) / st || st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st || st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st || st' ->
      (WHILE b DO c END) / st' || st'' ->
      (WHILE b DO c END) / st || st''
  | E_Acq_NHeld : forall st wl,
      isWlHeld wl st = false ->
      (ACQ wl) / st || cons wl st
  | E_Acq_Held : forall st wl,
      isWlHeld wl st = true ->
      (ACQ wl) / st || st
  | E_Rel_Held : forall st st' wl,
      (REL wl) / (st' ++ (cons wl st)) || (st' ++ st)
  | E_Rel_NHeld : forall st wl,
      isWlHeld wl st = false ->
      (REL wl) / st || st

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  | Case_aux c "E_Acq_NHeld" | Case_aux c "E_Acq_Held"
  | Case_aux c "E_Rel_Held" | Case_aux c "E_Rel_NHeld"].

Inductive isAcq : wakelock -> wlstate -> Prop := 
  | IA_Base : forall wl wls,
             isAcq wl (wl::wls).

Example ceval_example1:
    ((ACQ WL0);;
     IFB BIsHeld WL0
       THEN REL WL0
       ELSE SKIP
     FI)
   / empty_wlstate
   || empty_wlstate.
Proof.
  apply E_Seq with ([WL0]).
  Case "acquire command".
    apply E_Acq_NHeld. reflexivity.
  Case "if command".
    apply E_IfTrue.
      simpl. reflexivity.
      eapply E_Rel_Held with (st':=[]).
Qed.

(* No acquire wakelocks, programs that don't acquire a wakelock will not have any sleep bug *)
Inductive no_acq_wake: com -> Prop :=
 | no_acq_wakeSkip : 
     no_acq_wake(SKIP)
 (*| no_acq_wakeAss : forall s1 s2, no_acq_wake( s1 ::= s2)*)
 | no_acq_wakeSeq : 
     forall (c1 c2: com), 
       no_acq_wake(c1) -> 
       no_acq_wake(c2) -> 
       no_acq_wake(c1;;c2)
 | no_acq_wakeIf : 
     forall (b: bexp) (c1 c2: com), 
       no_acq_wake(c1) -> 
       no_acq_wake(c2) -> 
       (no_acq_wake (IFB b THEN c1 ELSE c2 FI))
 | no_acq_wakeWhile : 
     forall (b: bexp) (c: com), 
       no_acq_wake(c) -> 
       (no_acq_wake (WHILE b DO c END))
 | no_acq_wakeRel : 
     forall wl, no_acq_wake(REL wl).

Tactic Notation "no_acq_wake_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP"
 | Case_aux c ";;" 
 | Case_aux c "IFB"
 | Case_aux c "WHILE"
 | Case_aux c "REL" ].


Fixpoint no_acq_wakeF (c : com) : bool :=
  match c with
  | SKIP       => true
  | c1 ;; c2  => andb (no_acq_wakeF c1) (no_acq_wakeF c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_acq_wakeF ct) (no_acq_wakeF cf)
  | WHILE _ DO ct END  => no_acq_wakeF ct
  | REL _ => true
  | ACQ _ => false
  end.

Example noAcquiredWakelock:
    no_acq_wake((SKIP);;
     IFB BIsHeld WL0
       THEN REL WL0
       ELSE SKIP
     FI).
Proof.
  repeat constructor.
Qed.

Example noAcquiredWakelockF:
    no_acq_wakeF((SKIP);;
     IFB BIsHeld WL0
       THEN REL WL0
       ELSE SKIP
     FI) = true.
Proof.
  reflexivity.
Qed.

Theorem no_acq_eqv:
   forall c, no_acq_wakeF c = true <-> no_acq_wake c.
Proof with auto.
  intros.
  split.
  (*->*)
  com_cases (induction c) Case; intros; try constructor; auto;
  simpl in H; inversion H; 
  (** Seq and IFB cases **)
  rewrite andb_true_iff in H1; inversion H1; auto.
  (*<-*)
  intros. no_acq_wake_cases (induction H) Case; try reflexivity; try assumption;
  (** Seq and IFB cases **)
  try (apply andb_true_intro; split; assumption).
Qed.

Inductive protected : com -> wlstate -> Prop := 
  | P_Skip : forall wl st, protected SKIP (cons wl st)
  | P_Seq : forall c1 c2 st st',
      protected c1 st ->
      c1 / st  || st' ->
      protected c2 st' ->
      protected (c1 ;; c2) st
  | P_IfTrue : forall st b c1 c2,
      beval st b = true ->
      protected c1 st ->
      protected (IFB b THEN c1 ELSE c2 FI) st
  | P_IfFalse : forall st b c1 c2,
      beval st b = false ->
      protected c2 st ->
      protected (IFB b THEN c1 ELSE c2 FI) st
  | P_WhileEnd : forall l st' b c,
      beval (l :: st') b = false ->
      protected (WHILE b DO c END) (l :: st')
  | P_WhileLoop : forall st st' b c,
      beval st b = true ->
      c / st || st' ->
      protected (WHILE b DO c END) st' ->
      protected (WHILE b DO c END) st
  | P_Acq : forall st wl,
      protected (ACQ wl) st
  | P_Rel : forall wl wl' wl'' st,
      protected (REL wl) (cons wl' (cons wl'' st)).

(** Inductive onestep : process -> process -> Prop :=

(** This emulates the processor, the processor takes a list of process and
executes either one of them at random *)
Inductive processor : list process -> list process -> Prop := *) 

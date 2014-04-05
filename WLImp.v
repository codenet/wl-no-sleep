Require Export SfLib.

(** WLImp only has wakelock related statements and control flow statements *)

Module WakeLock.

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

Fixpoint isWlHeld (wl: wakelock) (st: wlstate) : bool := 
  match st with 
  | [] => false
  | cons wl' st' => if ( eq_wl_dec wl wl' ) then true
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
  | CRel : wakelock -> com                   (** Release wakelock *)
  | CCritical : com -> com.                  (** Critical statements *)

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
Notation "'{{' c '}}'" :=
  (CCritical c) (at level 80, right associativity).


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
  | E_Acq : forall st wl,
      (ACQ wl) / st || cons wl st
  | E_Rel : forall st st' wl,
      (REL wl) / (st' ++ (cons wl st)) || (st' ++ st)
  | E_Critical : forall st st' c,
      c / st || st' -> {{ c }} / st || st'


  where "c1 '/' st '||' st'" := (ceval c1 st st').

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
    apply E_Acq. 
  Case "if command".
    apply E_IfTrue.
      simpl. reflexivity.
      apply E_Rel with (st':=[]).
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
  | P_WhileEnd : forall b c,
      beval st b = false ->
      protected (WHILE b DO c END) (cons _ _)
  | P_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st || st' ->
      protected (WHILE b DO c END) st' ->
      protected (WHILE b DO c END) st
  | P_Acq : forall st wl,
      protected (ACQ wl) st
  | P_Rel : forall wl wl' wl'' st',
      protected (REL wl) (cons wl' (cons wl'' st))
  | P_Critical : forall st st' c,
      protected SKIP st ->           (** Should be protected in beginning *)
      protected c st ->              (** Command should be protected *)
      c / st || st' ->
      protected SKIP st' ->          (** Should be protected in end *)
      protected {{ c }} st.

(** Inductive onestep : process -> process -> Prop :=

(** This emulates the processor, the processor takes a list of process and
executes either one of them at random *)
Inductive processor : list process -> list process -> Prop := *)

End WakeLock.
 

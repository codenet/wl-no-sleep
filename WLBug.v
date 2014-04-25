Require Export WLImp.
Require Export WLHoare.
Require Export WLDup.
Require Export WLUtil.
Require Export Coq.Sets.Ensembles.
Require Export Util.

(** Definition of bug and correct program *)
Inductive no_bug: Assertion := 
  | No_Bug: no_bug empty_wlstate. 

Hint Constructors no_bug.

(*We define a correct program as a program that starts in a no_bug state 
(empty_wlstate, the list of wakelocks is empty) and after a command it also ends up in a no_bug state*)
Definition correct_program (c: com) : Prop :=
  {{ no_bug }} c {{ no_bug }}.

Hint Unfold correct_program.

(* If we have a program that doesn't acquire any wakelock then we can conclude that is a correct program*)
Theorem no_acq_no_bug : forall c,
  no_acq_wake c -> correct_program c.
Proof.
  intros c H.
  unfold correct_program; 
  unfold hoare_triple; 
  intros st st' Heval Hpre.
  
  ceval_cases (induction Heval) Case; try auto; inversion H; subst.
  (*Case E_Seq*)
  apply IHHeval2. assumption.
  apply IHHeval1; assumption. 
  (*Case E_IfTrue*)
  apply IHHeval; assumption.
  (*Case E_IfFalse*)
  apply IHHeval; assumption.
  (*Case E_WhileLoop*)
  apply IHHeval2. assumption.
  apply IHHeval1; assumption.  
  (*Case E_Rel_Held*)
  inversion Hpre. 
  unfold empty_wlstate in H1.
  apply app_cons_not_nil in H1.
  contradiction.  
Qed.

(*We define wl_set as a set of wakelocks using built in Coq Ensembles.*)
Definition wl_set : Type := Ensemble wakelock.
Definition wl_empty_set : wl_set := Empty_set wakelock.

(* We define the action of Gen of the reaching definition for every command using conservative analysis.*)
Inductive gen : com -> wl_set -> Prop := 
  | G_SKIP : gen SKIP wl_empty_set
  | G_Acq : forall wl,
      gen (ACQ wl) (Add wakelock wl_empty_set wl)
  | G_Rel : forall wl,
      gen (REL wl) wl_empty_set
  | G_Seq : forall c1 c2 wls wls' wls'',
      gen c1 wls ->
      gen c2 wls' ->
      kill c2 wls'' ->
      gen (c1 ;; c2) (Union wakelock wls (Setminus wakelock wls' wls''))
  | G_If : forall b c1 c2 wls wls',
      gen c1 wls ->
      gen c2 wls' ->
      gen (IFB b THEN c1 ELSE c2 FI) (Union wakelock wls wls')
  | G_While : forall b c wls, 
      gen c wls -> gen (WHILE b DO c END) wls

(* We define the action of Kill of the reaching definition for every command using conservative analysis.*)
with kill : com -> wl_set -> Prop := 
  | K_SKIP : kill SKIP wl_empty_set
  | K_Acq : forall wl,
      kill (ACQ wl) wl_empty_set
  | K_Rel : forall wl,
      kill (REL wl) (Add wakelock wl_empty_set wl)
  | K_Seq : forall c1 c2 wls wls' wls'',
      kill c1 wls ->
      kill c2 wls' ->
      gen c2 wls'' ->
      kill (c1 ;; c2) (Union wakelock wls (Setminus wakelock wls' wls''))
  | K_If : forall b c1 c2 wls wls',
      kill c1 wls ->
      kill c2 wls' ->
      kill (IFB b THEN c1 ELSE c2 FI) (Intersection wakelock wls wls')
  | K_While : forall b c, kill (WHILE b DO c END) wl_empty_set.

(* Example of a program that acquires a wakelock but only release it in one branch of the IF
   so kill will generate a wl_empty_set because we are using conservative analysis.*)
Example test_kill_1 :
  kill ((ACQ WL0);;
     IFB BIsHeld WL0
       THEN REL WL0
       ELSE SKIP
     FI) wl_empty_set.
Proof.
  replace wl_empty_set with 
  (Union wakelock wl_empty_set (Setminus wakelock wl_empty_set wl_empty_set)).
  apply K_Seq. constructor.
  replace wl_empty_set with 
    (Intersection wakelock (Add wakelock wl_empty_set WL0) wl_empty_set).
  apply K_If. apply K_Rel. apply K_SKIP.
  
  apply empty_intersect. 
  replace wl_empty_set with (Union wakelock wl_empty_set wl_empty_set).
  
  apply G_If. constructor. constructor. apply empty_union. rewrite empty_minus.
  apply empty_union.
Qed.

(* Example of a program that acquires a wakelock but only release it in one branch of the IF
   so gen will generate a wl_set containing WL0 because we are using conservative analysis.*)
Example test_gen_1 :
  gen ((ACQ WL0);;
     IFB BIsHeld WL0
       THEN REL WL0
       ELSE SKIP
     FI) (Add wakelock wl_empty_set WL0).
Proof.
  replace (Add wakelock wl_empty_set WL0) 
      with (Union wakelock (Add wakelock wl_empty_set WL0) 
                  (Setminus wakelock wl_empty_set wl_empty_set)).
  apply G_Seq. constructor.
  replace wl_empty_set with 
    (Union wakelock wl_empty_set wl_empty_set).
  apply G_If. apply G_Rel. apply G_SKIP.
  
  apply empty_union. 
  replace (wl_empty_set) 
      with (Intersection wakelock (Add wakelock wl_empty_set WL0) wl_empty_set).

  apply K_If. constructor. constructor. apply empty_intersect.
  rewrite empty_minus. rewrite union_commute. apply empty_S_union.
Qed.

(* single_stmt refers to those commands that are not composed of other commands.*)
Inductive single_stmt : com -> Prop :=
  | SS_Skip : single_stmt SKIP
  | SS_Acq : forall wl, single_stmt (ACQ wl)
  | SS_Rel : forall wl, single_stmt (REL wl).

(* We define the action of out of the reaching definition for every command using conservative analysis.*)
Inductive out : com -> wl_set -> wl_set -> Prop :=
     | O_SS : forall wli wlg wlk c, 
                single_stmt c ->
                gen c wlg ->
                kill c wlk ->
                out c wli (Union wakelock wlg (Setminus wakelock wli wlk))
     | O_Seq : forall wli wls wlo c1 c2,
                out c1 wli wls ->
                out c2 wls wlo ->
                out (c1;;c2) wli wlo
     | O_If : forall wli wlo1 wlo2 b c1 c2,
                out c1 wli wlo1 ->
                out c2 wli wlo2 ->
                out (IFB b THEN c1 ELSE c2 FI) wli (Union wakelock wlo1 wlo2)
     | O_While : forall wli wlg wlo b c,
                out c (Union wakelock wli wlg) wlo ->
                out (WHILE b DO c END) wli wlo.

Notation "<< P >>  c  << Q >>" :=
  (out c P Q) (at level 90, c at next level).

(* Program example that goes from a wl_empty_set to a wl_set that contains the 
   wakelock WL0 to test the out inductive definition, possible sleep bug program*)
Example test_flow_1 :
  << wl_empty_set >>
      ((ACQ WL0);;
     IFB BIsHeld WL0
       THEN REL WL0
       ELSE SKIP
     FI)
  << (Add wakelock wl_empty_set WL0) >>.
Proof. 
  eapply O_Seq.
  apply O_SS.
  constructor.
  constructor.
  constructor.
  rewrite empty_minus. rewrite union_commute. rewrite empty_S_union.
  apply O_If.
  remember (Add wakelock wl_empty_set WL0) as wli. 
  replace (wl_empty_set) 
    with (Union wakelock wl_empty_set (Setminus wakelock (Add wakelock wl_empty_set WL0) (Add wakelock wl_empty_set WL0))).
  subst.
  apply O_SS. constructor. constructor. constructor. rewrite same_minus. apply empty_union. 

  replace (Singleton wakelock WL0) 
  with (Union wakelock wl_empty_set (Setminus wakelock (Add wakelock wl_empty_set WL0) wl_empty_set)).

  apply O_SS. constructor. constructor. constructor. rewrite empty_S_minus. 
  rewrite empty_S_union. unfold Add. apply empty_S_union.
Qed.

Lemma flow_to_empty: forall c wls,
  ( << wls >> c << wl_empty_set >> ) -> 
  ( << wl_empty_set >> c << wl_empty_set >>).
Admitted.

(*Program example that goes from a wl_empty_set to a wl_empty_set using the out inductive definitions, 
  no sleep bug in this program*)
Example test_flow_2 :
  << wl_empty_set >>
      ((ACQ WL0);;(REL WL0))
  << wl_empty_set >>.
Proof.
  eapply O_Seq.
  apply O_SS. constructor. constructor. constructor.
  rewrite empty_minus. rewrite union_commute. rewrite empty_S_union.
  remember (Add wakelock wl_empty_set WL0) as wli. 
  replace (wl_empty_set) 
    with (Union wakelock wl_empty_set (Setminus wakelock (Add wakelock wl_empty_set WL0) (Add wakelock wl_empty_set WL0))).
  subst.  apply O_SS; constructor. rewrite same_minus. apply empty_union.
Qed.


Inductive subset : wl_set -> wlstate -> Prop :=
  | Subset_Nil : forall wl_s, subset wl_s empty_wlstate
  | Subset_Set_Add : forall wl wl_s wls,
             subset wl_s wls ->
             subset (Add wakelock wl_s wl) wls
  | Subset_Both_Add : forall wl wl_s wls,
             subset wl_s wls ->
             subset (Add wakelock wl_s wl) (wl :: wls). 

Tactic Notation "subset_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Nil" 
  | Case_aux c "Set_Add" 
  | Case_aux c "Both_Add" ].

Lemma subset_empty : subset wl_empty_set empty_wlstate.
Proof.
  constructor.
Qed.

Lemma subset_empty_2 : forall wls,
  subset wl_empty_set wls -> wls = empty_wlstate.
Proof.
  intros wls H.
  subset_cases (inversion H) Case. 
  try auto. 

  assert (Hcontra : In wakelock wl_empty_set wl).
    rewrite <- H0. unfold In. unfold Add. 
    apply Union_intror.
    unfold In. constructor.
  inversion Hcontra.

  assert (Hcontra : In wakelock wl_empty_set wl).
    rewrite <- H0. unfold In. unfold Add. 
    apply Union_intror.
    unfold In. constructor.
  inversion Hcontra.
Qed.

Lemma subset_union : forall wl_s1 wl_s2 wls,
  subset wl_s1 wls -> subset (Union wakelock wl_s1 wl_s2) wls.
Proof.
  intros wl_s1 wl_s2 wls H.
Admitted.

Lemma subset_union_2 : forall wl_s1 wls1 wl,
  subset wl_s1 wls1 ->
  subset (Union wakelock (Add wakelock wl_empty_set wl) wl_s1) (wl :: wls1).
Admitted.

Lemma subset_minus : forall wl_s wls wl,
  isWlHeld wl wls = false ->
  subset wl_s wls ->
  subset (Setminus wakelock wl_s (Add wakelock wl_empty_set wl)) wls.
Admitted.

Lemma subset_rm : forall wl st st' wl_s,
  subset wl_s (st ++ wl :: st') ->
  subset wl_s (st ++ st').
Admitted.


Theorem flow_subset : forall c wl_s1 wl_s2 wls1 wls2,
  no_duplicate wls1 ->
  subset wl_s1 wls1 ->
  (<< wl_s1 >> c << wl_s2 >>) ->
  (c / wls1 || wls2 ) ->
  subset wl_s2 wls2.
Proof.
  intros c.

  com_cases (induction c) Case; subst; 
  intros  wl_s1 wl_s2 wls1 wls2 Hdup Hset Hflow Heval.  

  (* SKIP *)
  inversion Heval; subst.
  inversion Hflow; subst. 
  inversion H0; subst.
  inversion H1; subst. 
  rewrite empty_S_minus.
  rewrite empty_S_union.
  assumption.
  
  (* SEQ *)
  inversion Heval; subst.
  inversion Hflow; subst.
  inversion H.
  apply IHc2 with (wl_s1:= wls)(wls1:=st'). 
  apply never_dup in H1. apply H1. assumption.
  apply IHc1 with (wl_s1:= wl_s1)(wls1:=wls1). 
  assumption. assumption. assumption. assumption. assumption. assumption.

  (* IFB *)
  inversion Heval; subst.
  (* true *)
  inversion Hflow; subst.
  inversion H.
  apply subset_union.
  apply IHc1 with (wl_s1:= wl_s1)(wls1:=wls1). 
  assumption. assumption. assumption. assumption.

  (* false *)
  inversion Hflow; subst.
  inversion H.
  rewrite union_commute.
  apply subset_union.
  apply IHc2 with (wl_s1:= wl_s1)(wls1:=wls1). 
  assumption. assumption. assumption. assumption.

  (**WHILE
  inversion Heval; subst.
  inversion Hflow; subst.
  inversion H.
  apply IHc with (wl_s1:=wl_s1)(wls1:=wls2).
  assumption.**)
  admit.

  (* ACQ *)
  inversion Heval; subst.
  inversion Hflow; subst.
  inversion H1; inversion H2; subst.
  rewrite empty_S_minus.
  apply subset_union_2.
  assumption.

  inversion Hflow; subst.
  inversion H1; inversion H2; subst.
  rewrite empty_S_minus.
  rewrite union_commute.
  apply subset_union.
  assumption.

  (* REL *)
  inversion Heval; subst.
  inversion Hflow; subst.
  inversion H0; inversion H1; subst.
  apply no_dup_rm in Hdup.
  rewrite empty_S_union.
  apply subset_minus.
  assumption.
  eapply subset_rm.
  apply Hset.
  inversion Hflow; subst.
  inversion H1; inversion H2; subst.
  rewrite empty_S_union.
  apply subset_minus.
  assumption.
  assumption.
Qed.

(*Theorem that states that if a program goes from a wl_empty_set 
  to another wl_empty_sey then we know it is a correct program.*)
Theorem flow_no_bug : forall c,
  (<< wl_empty_set >> c << wl_empty_set >>) ->
  (correct_program c).
Proof.
  intros c H st st' Heval Hpre. 
  unfold correct_program. 
  unfold hoare_triple.
  inversion Hpre; subst.
  assert ( Hempty : subset wl_empty_set st' ). 
    eapply flow_subset with (wls1:=empty_wlstate)(wl_s1:=wl_empty_set)(c:=c).
    constructor.
    apply subset_empty.
    assumption.
    assumption.
  
  apply subset_empty_2 in Hempty. subst. constructor.
Qed.
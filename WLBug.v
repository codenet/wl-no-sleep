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

Tactic Notation "ss_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SS_Skip" 
  | Case_aux c "SS_Acq" 
  | Case_aux c "SS_Rel" ].


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
     (**| O_WhileInv : forall wli b c,
                out c wli wli ->
                out (WHILE b DO c END) wli wli.**)
     | O_While : forall wli wlo b c,
                out c wli wlo ->
                out (WHILE b DO c END) wli (Union wakelock wli wlo).

     (**| O_While : forall wli wlg wlo b c,
                gen c wlg ->
                out c (Union wakelock wli wlg) wlo ->
                out (WHILE b DO c END) wli wlo.**)

Tactic Notation "out_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "O_SS" 
  | Case_aux c "O_Seq" 
  | Case_aux c "O_If"
  | Case_aux c "O_WhileInv" ].
  (*| Case_aux c "O_WhileVar" ].*)


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
  | Subset_Ind : forall wl wl_s wls,
             subset wl_s wls ->
             In wakelock wl_s wl ->
             subset wl_s (wl :: wls). 

Tactic Notation "subset_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Nil" 
  | Case_aux c "Set_Ind" ].

Lemma subset_empty : subset wl_empty_set empty_wlstate.
Proof.
  constructor.
Qed.

Lemma subset_empty_2 : forall wls,
  subset wl_empty_set wls -> wls = empty_wlstate.
Proof.
  intros wls H.
  subset_cases (inversion H) Case; try auto; try solve by inversion.
Qed.

Lemma subset_union : forall wl_s1 wl_s2 wls,
  subset wl_s1 wls -> subset (Union wakelock wl_s1 wl_s2) wls.
Proof.
  intros wl_s1 wl_s2 wls H.
  induction H; subst.
  constructor.
  constructor. assumption. apply Union_introl. assumption.
Qed.

Lemma subset_add : forall wl_s1 wls1 wl,
  subset wl_s1 wls1 ->
  subset (Add wakelock wl_s1 wl) (wl :: wls1).
Proof.
  intros wl_s1 wls1 wl H.
  constructor.
  induction wls1.
  constructor.
  inversion H; subst.
  constructor. apply IHwls1.  assumption.
  apply Union_introl. assumption.
  apply Union_intror. constructor.
Qed.  

Lemma subset_union_2 : forall wl_s1 wls1 wl,
  subset wl_s1 wls1 ->
  subset (Union wakelock (Add wakelock wl_empty_set wl) wl_s1) (wl :: wls1).
Proof.
  intros wl_s1 wls1 wl H.
  rewrite add_union. rewrite empty_S_union.  apply subset_add. assumption.
Qed.

Lemma subset_minus : forall wl_s wls wl,
  isWlHeld wl wls = false ->
  subset wl_s wls ->
  subset (Setminus wakelock wl_s (Add wakelock wl_empty_set wl)) wls.
Proof.
  intros wl_s wls.
  induction wls as [| wl0 wls'].
  constructor.
  intros wl Hheld Hset.
  destruct (eq_wl_dec wl wl0).
  Case "wl = wl0". subst.
    simpl in Hheld. rewrite <- beq_wl_refl in Hheld. inversion Hheld.
  Case "wl <> wl0".
    inversion Hset; subst.
    constructor. apply IHwls'. 
    simpl in Hheld. apply beq_wl_false_iff in n.
    rewrite n in Hheld. assumption. assumption.
    apply in_minus; assumption.
Qed.

Lemma subset_rm : forall wl st st' wl_s,
  subset wl_s (st ++ wl :: st') ->
  subset wl_s (st ++ st').
Proof.
  intros wl st.
  induction st as [|wl0 st0]; intros st' wl_s H.
  Case "[]".
    simpl.
    inversion H; subst. assumption.
  Case "wl0 :: st0".
    inversion H; subst.
    rewrite <- app_comm_cons.
    constructor.
    apply IHst0.
    rewrite <- app_comm_cons in H.  
    assumption.
    assumption.
Qed.

Theorem out_total_function: forall c wli,
  exists wlo, (out c wli wlo).
Proof.
  intros c.
  com_cases (induction c) Case; intros wli. 

  (* SKIP *)
  exists wli.
  assert( H: (Union wakelock wl_empty_set (Setminus wakelock wli wl_empty_set)) = wli ).
    rewrite empty_S_minus.
    rewrite empty_S_union.
    reflexivity.
  rewrite <- H at 2.
  apply O_SS; constructor.

  (* SEQ *)
  destruct IHc1 with (wli:=wli) as [wls].
  destruct IHc2 with (wli:=wls) as [wlo].
  exists wlo.
  eapply O_Seq. apply H. assumption.
  
  (* IFB *)
  destruct IHc1 with (wli:=wli) as [wlo1].
  destruct IHc2 with (wli:=wli) as [wlo2].
  exists (Union wakelock wlo1 wlo2).
  constructor; assumption.

  (* WHILE *)
  destruct IHc with (wli:=wli) as [wlo].
  exists (Union wakelock wli wlo).
  constructor; assumption.

  (* ACQ *)
  exists (Union wakelock (Add wakelock wl_empty_set w) 
                 (Setminus wakelock wli wl_empty_set)).
  constructor; constructor.

  (* REL *)
  exists (Union wakelock wl_empty_set
                 (Setminus wakelock wli (Add wakelock wl_empty_set w))).
  constructor; constructor.
Qed.

Theorem out_deterministic: forall c wli wlo wlo',
  out c wli wlo ->
  out c wli wlo' ->
  wlo = wlo'.
Proof.
  intros c.
  com_cases (induction c) Case; intros wli wlo wlo' H H';
  (* Solve SS cases *)
  try (inversion H; inversion H'; subst;
  inversion H7; inversion H8; inversion H1; inversion H2; subst; reflexivity);
  (* Remove O_SS constructor from other cases *)
  inversion H; try solve by inversion; 
  inversion H'; try solve by inversion; subst.

  Case ";;".
  assert (Hs : wls = wls0 ).
    eapply IHc1; eassumption.
  subst.
  eapply IHc2; eassumption.

  Case "IFB".
  assert (Hs : wlo0 = wlo1 ).
    eapply IHc1; eassumption.
  assert (Hs' : wlo2 = wlo3 ).
    eapply IHc2; eassumption.
  subst.
  reflexivity.
  
  Case "WHILE".
  assert (Hs : wlo0 = wlo1 ).
    eapply IHc; eassumption.
  subst.
  reflexivity.
Qed.

Lemma flow_is_set_ops : forall c, exists wla wlb, forall wli,
  << wli >> c << (Union wakelock wlb (Setminus wakelock wli wla)) >>.
Proof with auto.
  intros c.
  com_cases (induction c) Case; 
  (** Solve O_SS cases *)
  try (eexists; eexists; intros wli; apply O_SS; econstructor).

  Case ";;".
    inversion_clear IHc1; inversion_clear H.
    rename x into wla1. rename x0 into wlb1.

    inversion_clear IHc2; inversion_clear H.
    rename x into wla2. rename x0 into wlb2.

    (** We know that -
    wls = (wlb1 U (wli - wla1)) and
    wlo = (wlb2 U (wls - wla2)). 
    ->
    wlo = (wlb2 U ((wlb1 U (wli - wla1)) - wla2))
    For wlo = (wlb U (wli - wla)) to hold,
      wla = (wla2 U wla1)
      wlb = (wlb2 U (wlb1 - wla2) )
    **)
    remember (Union wakelock wla2 wla1) as wla.
    remember (Union wakelock wlb2 (Setminus wakelock wlb1 wla2)) as wlb.
    exists wla. 
    exists wlb. 
    intros wli.
    eapply O_Seq. apply H0.

    assert ( HU : Union wakelock wlb (Setminus wakelock wli wla)
             = 
             (Union wakelock wlb2 
                (Setminus wakelock
                   (Union wakelock wlb1 (Setminus wakelock wli wla1)) wla2) ) ).
      SCase "Pf of assert".
        apply Extensionality_Ensembles.
        split.
        SSCase "->".
          intros w Hi.
          inversion Hi; subst.
          inversion H; subst.
          apply Union_introl...
          inversion H2; subst.
          apply Union_intror.
          constructor.
          apply Union_introl...
          assumption.

          inversion H; subst.
          apply Union_intror.
          constructor.
          apply Union_intror.
          constructor.
          assumption.
          apply not_in_union in H3.
          inversion H3...
          apply not_in_union in H3.
          inversion H3...

        SSCase "<-".
          intros w Hi.
          inversion Hi; subst.
          apply Union_introl.
          apply Union_introl...
          inversion H; subst.
          inversion H2; subst.
          apply Union_introl.
          apply Union_intror.
          constructor...
          apply Union_intror.
          inversion H4.
          constructor...
          apply not_in_union...
    rewrite HU...

  Case "IFB".
    inversion_clear IHc1; inversion_clear H.
    rename x into wla1. rename x0 into wlb1.

    inversion_clear IHc2; inversion_clear H.
    rename x into wla2. rename x0 into wlb2.

    (** We know that -
    wlo1 = (wlb1 U (wli - wla1)) and
    wlo2 = (wlb2 U (wli - wla2)) and
    wlo = (wlo1 U wlo2). 
    ->
    wlo = (wlb1 U (wli - wla1)) U (wlb2 U (wli - wla2))
    ->
    wlo = wlb1 U wlb2 U (wli - wla1) U (wli - wla2)
    ->
    For wlo = (wlb U (wli - wla)) to hold,
      wla = ( wla1 ∩ wla2 )
      wlb = wlb1 U wlb2
    **)

    remember (Intersection wakelock wla1 wla2) as wla.
    remember (Union wakelock wlb1 wlb2) as wlb.
    exists wla. exists wlb. 
    intros wli.
    assert ( HU : 
      ( Union wakelock wlb (Setminus wakelock wli wla) )
      =
      (Union wakelock (Union wakelock wlb1 (Setminus wakelock wli wla1))
       (Union wakelock wlb2 (Setminus wakelock wli wla2))) ).
      SCase "Pf of assert".
        apply Extensionality_Ensembles.
        split.
        SSCase "->".
          intros w Hi.
          inversion Hi; subst.
          inversion H; subst.
          apply Union_introl.
          apply Union_introl...
          apply Union_intror.
          apply Union_introl...

          inversion H; subst.
          apply not_in_intersect in H3.
          inversion H3.
          apply Union_introl.
          apply Union_intror.
          constructor...
          apply Union_intror.
          apply Union_intror.
          constructor...
        SSCase "<-".
          intros w Hi.
          inversion Hi; subst.
          inversion H; subst.
          apply Union_introl.
          apply Union_introl...
          inversion H2; subst.
          apply Union_intror.
          constructor...
          intros Hinter.
          apply H4.
          inversion Hinter; subst...

          inversion H; subst.
          apply Union_introl.
          apply Union_intror...
          inversion H2; subst.
          apply Union_intror.
          constructor...
          intros Hinter.
          apply H4.
          inversion Hinter; subst...       
    rewrite HU.
    eapply O_If...
    
  Case "WHILE".
    inversion_clear IHc; inversion_clear H.
    rename x into wla1. rename x0 into wlb1.

    exists wl_empty_set. 
    exists wlb1. 
    intros wli.
    rewrite empty_S_minus.
    assert ( HU : Union wakelock wlb1 wli
                  = (Union wakelock wli 
                           (Union wakelock wlb1 (Setminus wakelock wli wla1))) ).
      SCase "Proof of assert".
      apply Extensionality_Ensembles.
      split.
      SSCase "->".
        intros w H.
        inversion H; subst.
        apply Union_intror. apply Union_introl...
        apply Union_introl...

      SSCase "<-".
        intros w H.
        inversion H; subst. 
        apply Union_intror...
        inversion H1; subst. 
        apply Union_introl...
        inversion H2; subst. 
        apply Union_intror...

    rewrite HU.
    apply O_While...
Qed.

Lemma flow_apply_twice_same : forall c wli wlo,
  << wli >> c << wlo >> ->
  << wlo >> c << wlo >>.
Proof with auto.
  intros c wli wlo H.
  pose proof (flow_is_set_ops c) as Hf.
  inversion_clear Hf; inversion_clear H0.
  rename x into wla. rename x0 into wlb.

  assert ( wlo = Union wakelock wlb (Setminus wakelock wli wla) ).
    apply (out_deterministic c wli)...
    
  assert ( wlo = Union wakelock wlb (Setminus wakelock wlo wla) ).
    rewrite H0.
    apply Extensionality_Ensembles.
    split.
    Case "->".
      intros w Hi.
      inversion Hi; subst.
      apply Union_introl...
      inversion Hi; subst.
      apply Union_introl...
      inversion H0; subst.
      apply Union_intror.
      constructor.
      apply Union_intror...
      assumption.

    Case "<-".
      intros w Hi.
      inversion Hi; subst.
      apply Union_introl...
      inversion H2; subst.
      assumption.
      
  rewrite H2 at 2.
  apply H1.
Qed.


Theorem flow_subset : forall c wl_s1 wl_s2 wls1 wls2,
  no_duplicate wls1 ->
  subset wl_s1 wls1 ->
  (<< wl_s1 >> c << wl_s2 >>) ->
  (c / wls1 || wls2 ) ->
  subset wl_s2 wls2.
Proof.
  intros c wl_s1 wl_s2 wls1 wls2 Hdup Hset Hflow Heval.
  generalize dependent wl_s2.
  generalize dependent wl_s1. 
  ceval_cases (induction Heval) Case; intros wl_s1 Hset wl_s2 Hflow.

  (* SKIP *)
  inversion Hflow; subst.
  inversion H0; inversion H1; subst.
  rewrite empty_S_minus.
  rewrite empty_S_union.
  assumption.

  (* SEQ *)
  inversion Hflow; subst.
  inversion H.
  apply IHHeval2 with (wl_s1:= wls). 
  apply never_dup in Heval1. apply Heval1. assumption.
  apply IHHeval1 with (wl_s1:= wl_s1). 
  assumption. assumption. assumption. assumption.

  (* IFB *)
  (* true *)
  inversion Hflow; subst.
  inversion H0.
  apply subset_union.
  apply IHHeval with (wl_s1:= wl_s1). 
  assumption. assumption. assumption. 

  (* false *)
  inversion Hflow; subst.
  inversion H0.
  rewrite union_commute.
  apply subset_union.
  apply IHHeval with (wl_s1:= wl_s1). 
  assumption. assumption. assumption. 

  (*While*)
  (* false *)
  inversion Hflow; subst.
  (* O_SS *)
  inversion H0.
  (* O_While *)
  apply subset_union.
  assumption.

  (* true *)
  inversion Hflow; subst.
  inversion H0.

  apply IHHeval2 with (wl_s1:=(Union wakelock wl_s1 wlo)).
  apply never_dup in Heval1. apply Heval1. assumption.
  rewrite union_commute.
  apply subset_union.
  eapply IHHeval1. assumption. apply Hset. assumption. 
  clear Heval1 Heval2 IHHeval1 IHHeval2 Hset H Hdup.
  eapply flow_apply_twice_same.
  apply Hflow.

  (* ACQ *)
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

Corollary flow_no_bug' : forall c,
  ~ (correct_program c) -> 
  ~ (<< wl_empty_set >> c << wl_empty_set >>).
Proof.
  intros c H1 H2.
  apply H1.
  apply flow_no_bug.
  assumption.
Qed.


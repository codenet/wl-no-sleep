Require Export WLImp.
Require Export WLHoare.
Require Export WLUtil.

Inductive no_duplicate : Assertion :=  
  | No_Empty: no_duplicate []
  | No_Ind : forall wl st,
               no_duplicate st -> 
               ~ appears_in wl st ->
               no_duplicate (wl :: st).


Lemma rm_isWlHeld: forall wl wl' st,
                   isWlHeld wl (wl' :: st) = false ->
                   isWlHeld wl st = false.
Proof.
  intros wl wl' st H.
  inversion H.
  destruct (eq_wl_dec wl wl') eqn:Hwl.
  SCase "wl = wl'". subst. rewrite <- beq_wl_refl in *. inversion H1.
  SCase "wl <> wl'". 
  assert (Heq: beq_wl wl wl' = false ). 
    apply beq_wl_false_iff. assumption.
  rewrite Heq in H1. rewrite Heq. reflexivity.
Qed.

Lemma rm_no_dup: forall wl st,
                   no_duplicate (wl :: st) -> no_duplicate st.
Proof.
  intros wl st H.
  inversion H. assumption.
Qed.

Lemma rm_appears_in: forall {X:Type} (x x' : X) lx lx',
                       ~ appears_in x' (lx ++ (x::lx')) ->
                       ~ appears_in x' (lx ++ lx').
Proof.
  intros X x x' lx lx' H Hcontra. apply H. clear H.
  induction lx as [| y ly].
  Case "[]". 
    simpl in *. constructor. assumption.
  Case "y :: ly".
    inversion Hcontra; subst.
    constructor. 
    constructor. auto.
Qed.

Lemma rm_mid_no_dup: forall wl st st',
                   no_duplicate (st ++ wl :: st') -> no_duplicate (st ++ st').
Proof.
  intros wl st st' H.
  induction st as [| wl' st''].
  Case "[]". simpl in *. eapply rm_no_dup. apply H.
  Case "wl' :: st''".
    apply No_Ind. apply IHst''. eapply rm_no_dup. apply H.
    clear IHst''. inversion H; subst. 
    apply (rm_appears_in wl wl' st'' st'). assumption.
Qed.

Lemma rm_appears : forall {X:Type} (x y : X) l,
                     appears_in x (y :: l) -> x <> y -> appears_in x l.
Proof.
  intros X x y l H1 H2.
  inversion H1.
  unfold not in H2.
  apply H2 in H0.
  contradiction.
  assumption.
Qed.

Lemma rm_not_appears : forall {X:Type} (x y : X) l,
                     ~appears_in x (y :: l) -> ~ appears_in x l.
Proof.
  intros X x y l H contra.
  apply H.
  constructor.
  assumption.
Qed.

Lemma isWlHeld_appear: forall wl st,
                          isWlHeld wl st = false <-> ~ appears_in wl st.
Proof.
  intros wl st.
  split.
  Case "->".
    intros H.
    intros contra.
    induction st as [| wl' st'].
    inversion contra.
    destruct (eq_wl_dec wl wl').
    SCase "wl = wl'".
      subst.
      unfold isWlHeld in H.
      rewrite <- beq_wl_refl in H.
      inversion H.
    SCase "wl <> wl'".
      apply IHst'.
      eapply rm_isWlHeld. apply H.
      eapply rm_appears. apply contra. assumption.

  Case "<-".
    intros H.
    induction st as [| wl' st'].
    reflexivity.
    assert( Hwl: beq_wl wl wl' = false ). 
      SCase "Pf of assert".
        apply beq_wl_false_iff.
        intros contra.
        apply H.
        subst.
        apply ai_here.

   unfold isWlHeld.
   rewrite Hwl.
   apply IHst'.
   eapply rm_not_appears. apply H.   
Qed.

Theorem never_dup : forall c,
  {{ no_duplicate }} c {{ no_duplicate }}.
Proof.
  intros c. unfold hoare_triple. 
  intros st st' Heval Hst.
  ceval_cases (induction Heval) Case; try auto. 
  apply No_Ind. assumption. 
  apply isWlHeld_appear. assumption.
  eapply rm_mid_no_dup. apply Hst.
Qed.

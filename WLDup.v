Require Export WLImp.
Require Export WLHoare.
Require Export WLUtil.

(*Asserts that there are no duplicate wakelocks in the wl_state*)
Inductive no_duplicate : Assertion :=  
  | No_Empty: no_duplicate []
  | No_Ind : forall wl st,
               no_duplicate st -> 
               ~ appears_in wl st ->
               no_duplicate (wl :: st).

Hint Resolve No_Empty No_Ind : wl.

(*Lemma that states if in wl_state(wakelock list), some wakelock (wl) is not held.
  If we remove a wakelock (wl') from that wl_state, then we know that the wakelock
 (wl) will also not be held in the resultin wl_state.*)
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

(*Lemma that states that if there are no duplicates in a wl_state list that includes the wakelock wl,
  then it will not be duplicates in a wl_state list that doesn't include it.*)
Lemma rm_no_dup: forall wl st,
                   no_duplicate (wl :: st) -> no_duplicate st.
Proof.
  intros wl st H.
  inversion H. assumption.
Qed.

(*Lemma that states that if some element x' doesn't appear in the concatenation of two lists 
  which one include the element x
  then it will not appear in the concatenation of those two lists not including the element x*)
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

(*Lemma that states that if in the concatenation of two lists and one includes 
  the element wl there are no duplicate wakelocks, then it will not be 
  duplicate wakelocks in the concatenation of those two lists without wl.*)
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

(* Lemma that states if the element x appears in the cons of the list l and the element y, 
   and the elements x and y are different, then x will appear in l.*)
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

(* Lemma that states if the element x does not appears in the cons of the list l and the element y, 
   then x will not appears in l.*)
Lemma rm_not_appears : forall {X:Type} (x y : X) l,
                     ~appears_in x (y :: l) -> ~ appears_in x l.
Proof.
  intros X x y l H contra.
  apply H.
  constructor.
  assumption.
Qed.

(* Lemma that states that a wakelock is not held iff it does not appears in the wlstate list.*)
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

(* Theorem that proves that if we start in a no_duplicate state(no duplicate wakelocks in the wlstate list, 
   forall possible programs we will only arrive to another no_duplicate state*)
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

Lemma no_dup_rm : forall wl st st',
  no_duplicate (st ++ wl :: st') ->
  isWlHeld wl (st ++ st') = false.
Admitted.
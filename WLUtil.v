Require Export WLImp.
Require Export WLHoare.

(*Lemma that states if we compare the same wakelock (wl) for equality yields always true.*)
Lemma beq_wl_refl: forall wl,
                       true = beq_wl wl wl.
Proof.
  destruct wl as [n]. 
  simpl. 
  apply beq_nat_refl.
Qed.

(*Lemma that states if two wakelocks (x,y) are equal beq_wl then those wakelocks are equal (x=y).*)
Lemma beq_wl_eq: 
  forall x y, true = beq_wl x y -> x = y.
Proof.
  intros x y H.
  destruct x as [n].   destruct y as [m].
  simpl in H. apply beq_nat_eq in H. subst. reflexivity.
Qed.

(*Lemma that states if for two wakelocks (x,y) beq_wl yields true iff those wakelocks are equal (x=y).*)
Lemma beq_wl_true_iff: 
  forall x y, beq_wl x y = true <-> x = y.
Proof.
  intros x y. 
  split; intros H; 
  destruct x as [n]; destruct y as [m]; simpl in H.
  apply beq_nat_true_iff in H; subst; reflexivity.
  rewrite H. rewrite <- beq_wl_refl. reflexivity.
Qed.

(*Lemma that states if for two wakelocks (x,y) beq_wl yields false iff those wakelocks are not equal (x<>y).*)
Lemma beq_wl_false_iff: 
  forall x y, beq_wl x y = false <-> x <> y.
Proof.
  intros x y.
  split; intros H; destruct x as [n]; destruct y as [m]; simpl in H.
  apply beq_nat_false_iff in H. intros contra. apply H. inversion contra. reflexivity.
  unfold beq_wl. apply beq_nat_false_iff. intros contra. apply H. subst. reflexivity.
Qed.

(*Lemma that states that the order of wakelocks in beq_wl don't change the result.*)
Lemma beq_wl_sym: 
  forall x y, beq_wl x y = beq_wl y x.
Proof.
  intros x y.
  destruct x as [n]; destruct y as [m].
  unfold beq_wl.
  apply beq_nat_sym.
Qed.
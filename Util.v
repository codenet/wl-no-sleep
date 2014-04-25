Require Export SfLib.
Require Export WLImp.
Require Export Coq.Sets.Ensembles.

(* Lemma that states that the intersection is commutative, B intersection C equals C intersection B.*)
Lemma intersect_commute: forall U B C, 
  (Intersection U B C) = (Intersection U C B).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set. split;
  unfold Included; intros u H; inversion H; apply Intersection_intro; 
  assumption; assumption.
Qed.

Hint Rewrite intersect_commute.

(* Lemma that states that the union is commutative, B union C equals C union B.*)
Lemma union_commute: forall U B C, 
  (Union U B C) = (Union U C B).
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set. split;
  unfold Included; intros u H; inversion H; 
  [apply Union_intror | apply Union_introl | apply Union_intror | apply Union_introl]; assumption.
Qed.

Hint Rewrite union_commute.

(*Lemma that states that the intersection of an empty set with another set (B) is always the empty set.*)
Lemma empty_intersect: forall U B, 
  (Intersection U B (Empty_set U)) = Empty_set U.
Proof.
  intros U B.
  apply Extensionality_Ensembles. 
  unfold Same_set. split; unfold Included; intros x H; inversion H; try assumption.
Qed.

Hint Rewrite empty_intersect.

(*Lemma that states that some set (S) minus an empty set is always that some set(S).*)
Lemma empty_S_minus: forall U S, 
  (Setminus U S (Empty_set U)) = S.
Proof.
  intros. 
  apply Extensionality_Ensembles. 
  unfold Same_set. split; unfold Included; intros x H.
  Case "left".
    unfold Setminus in H. inversion H. assumption.
  Case "right".
    unfold Setminus. split. assumption.
    intros Hcontra. inversion Hcontra.    
Qed.

Hint Rewrite empty_S_minus.

(*Lemma that states that the some set (S) minus an empty set is always that set(S).*)
Lemma empty_minus: forall U, 
  (Setminus U (Empty_set U) (Empty_set U)) = Empty_set U.
Proof.  
  intros U.
  apply empty_S_minus.
Qed.

Hint Rewrite empty_minus.

(* Lemma that states that some set (S) minus that same set (S) is always the empty set.*)
Lemma same_minus: forall U S, 
  (Setminus U S S) = Empty_set U.
Proof.
  intros.
  apply Extensionality_Ensembles.   
  unfold Same_set. split; unfold Included; intros x H.
  Case "left".
    unfold Setminus in H. inversion H. contradiction.
  Case "right".
    inversion H.
Qed.

Hint Rewrite same_minus.

(*Lemma that states that the empty set minus some set(S) is always the empty set.*)
Lemma empty_minus_S: forall U S, 
  (Setminus U (Empty_set U) (S)) = Empty_set U.
Proof.
  intros.
  apply Extensionality_Ensembles.   
  unfold Same_set. split; unfold Included; intros x H.
  Case "left".
    unfold Setminus in H. inversion H. assumption.
  Case "right".
    inversion H.
Qed.

Hint Rewrite empty_minus_S.

(*Lemma that states that the empty set union some set (S) is always that some set (S).*)
Lemma empty_S_union: forall U S, 
  (Union U (Empty_set U) S) = S.
Proof.
  intros.
  apply Extensionality_Ensembles.   
  unfold Same_set. split; unfold Included; intros x H.
  Case "left".
    inversion H. inversion H0. assumption.
  Case "right".
    apply Union_intror. assumption.
Qed.

Hint Rewrite empty_S_union.

(*Lemma that states that the union of two empty set is always de empty set*)
Lemma empty_union: forall U, 
  (Union U (Empty_set U) (Empty_set U)) = Empty_set U.
Proof.
  intros U. rewrite empty_S_union. reflexivity. Qed.

Hint Rewrite empty_union.

(*Lemma that states that if we know that union of some two sets (S1 and S2) is equal to the empty set.
  Then we can conclude that the first of those sets (S1) is equal to empty set.*)
Lemma S_S_union_empty: forall U S1 S2,
  Union U S1 S2 = (Empty_set U) -> 
  S1 = (Empty_set U).
Proof.
  intros U S1 S2 H.
  apply Extensionality_Ensembles. unfold Same_set. split.
  unfold Included. intros w. rewrite <- H. apply Union_introl.
  unfold Included. intros w. intros Hcontra. inversion Hcontra.
Qed.

Hint Rewrite S_S_union_empty.

(*Lemma that states if we compare the same wakelock (wl) for equality yields always true.*)
Lemma beq_wl_refl : forall wl,
  true = beq_wl wl wl.
Proof.
  intros. destruct wl as [n].
  unfold beq_wl. apply beq_nat_refl.
Qed.

Hint Rewrite beq_wl_refl.
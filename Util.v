Require Export SfLib.
Require Export WLImp.
Require Export Coq.Sets.Ensembles.

Lemma intersect_commute: forall U B C, 
  (Intersection U B C) = (Intersection U C B).
  Admitted.

Lemma union_commute: forall U B C, 
  (Union U B C) = (Union U C B).
  Admitted.

Lemma empty_intersect: forall U B, 
  (Intersection U B (Empty_set U)) = Empty_set U.
  intros U B.
  apply Extensionality_Ensembles. 
  unfold Same_set. split.
  Case "left".
    unfold Included. intros x H. 

    Admitted.

Lemma empty_S_minus: forall U S, 
  (Setminus U S (Empty_set U)) = S.
    Admitted.


Lemma empty_minus: forall U, 
  (Setminus U (Empty_set U) (Empty_set U)) = Empty_set U.
Proof.  
  intros U.
  apply empty_S_minus.
Qed.

Lemma same_minus: forall U S, 
  (Setminus U S S) = Empty_set U.
    Admitted.

Lemma empty_minus_S: forall U S, 
  (Setminus U (Empty_set U) (S)) = Empty_set U.
    Admitted.


Lemma empty_S_union: forall U S, 
  (Union U (Empty_set U) S) = S.
    Admitted.

Lemma empty_union: forall U, 
  (Union U (Empty_set U) (Empty_set U)) = Empty_set U.
Proof.
  intros U. rewrite empty_S_union. reflexivity. Qed.

Lemma S_S_union_empty: forall U S1 S2,
  Union U S1 S2 = (Empty_set U) -> 
  S1 = (Empty_set U).
Proof.
  intros U S1 S2 H.
  apply Extensionality_Ensembles. unfold Same_set. split.
  unfold Included. intros w. rewrite <- H. apply Union_introl.
  unfold Included. intros w. intros Hcontra. inversion Hcontra.
Qed.

Lemma beq_wl_refl : forall wl,
                      true = beq_wl wl wl.
Proof.
  Admitted.
Require Export SfLib.
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

Lemma empty_minus: forall U, 
  (Setminus U (Empty_set U) (Empty_set U)) = Empty_set U.
    Admitted.


Lemma empty_S_union: forall U S, 
  (Union U (Empty_set U) S) = S.
    Admitted.

Lemma empty_union: forall U, 
  (Union U (Empty_set U) (Empty_set U)) = Empty_set U.
Proof.
  intros U. rewrite empty_S_union. reflexivity. Qed.


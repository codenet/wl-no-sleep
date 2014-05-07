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

Hint Resolve intersect_commute : ensemble.

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

Hint Resolve union_commute : ensemble.

(*Lemma that states that the intersection of an empty set with another set (B) is always the empty set.*)
Lemma empty_intersect: forall U B, 
  (Intersection U B (Empty_set U)) = Empty_set U.
Proof.
  intros U B.
  apply Extensionality_Ensembles. 
  unfold Same_set. split; unfold Included; intros x H; inversion H; try assumption.
Qed.

Hint Resolve empty_intersect : ensemble.

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

Hint Resolve empty_S_minus : ensemble.

(*Lemma that states that the some set (S) minus an empty set is always that set(S).*)
Lemma empty_minus: forall U, 
  (Setminus U (Empty_set U) (Empty_set U)) = Empty_set U.
Proof.  
  intros U.
  apply empty_S_minus.
Qed.

Hint Resolve empty_minus : ensemble.

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

Hint Resolve same_minus : ensemble.

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

Hint Resolve empty_minus_S : ensemble.

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

Hint Resolve empty_S_union : ensemble.

(*Lemma that states that the union of two empty set is always de empty set*)
Lemma empty_union: forall U, 
  (Union U (Empty_set U) (Empty_set U)) = Empty_set U.
Proof.
  intros U. rewrite empty_S_union. reflexivity. Qed.

Hint Resolve empty_union : ensemble.

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

Hint Resolve S_S_union_empty : ensemble.

(* Lemma that states that a set (S1) plus and element (u) union another set (S2) 
   is the same as the union of the two sets (S1 and S2) and the addittion of the element (u) *)
Lemma add_union : forall U S1 S2 u,
  Union U (Add U S1 u) S2 = Add U (Union U S1 S2) u.
Proof.
  intros U S1 S2 u.
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  unfold In.
  unfold Add.
  split.
  intros. inversion H. inversion H0.   apply Union_introl. apply Union_introl. assumption.
  apply Union_intror. assumption.
  apply Union_introl. apply Union_intror. assumption.
  intros. inversion H. inversion H0. apply Union_introl. apply Union_introl. assumption.
  apply Union_intror. assumption.
  apply Union_introl. apply Union_intror. assumption.
Qed.

Hint Resolve add_union : ensemble.

Lemma in_minus : forall X x y s,
  x <> y ->
  In X s y ->
  In X (Setminus X s (Add X (Empty_set X) x)) y.
Proof.
  intros X x y s Hxy Hin.
  split.
  assumption.
  intros contra.
  inversion contra; subst; inversion H; subst.
  apply Hxy. reflexivity.
Qed.

Hint Resolve in_minus : ensemble.

Lemma same_union : forall X s,
  Union X s s = s.
Proof.
  intros.  
  apply Extensionality_Ensembles.
  unfold Same_set.
  unfold Included.
  split; intros.
  inversion H; apply H0.
  apply Union_intror.
  assumption.
Qed.

Hint Resolve same_union : ensemble.

Axiom de_morgan_not_and_not : forall P Q:Prop,
  ~(P /\ Q) -> (~P \/ ~Q).

Lemma not_in_intersect : forall X x s1 s2,
  ~ In X (Intersection X s1 s2) x <-> ~ (In X s1 x) \/ ~ (In X s2 x).
Proof.
  intros.
  split.
  intros.
  (* -> *)  
  apply de_morgan_not_and_not with (P:= (In X s1 x))(Q:= (In X s2 x)).
  unfold not in *.
  intros.
  apply H.
  inversion H0.
  constructor; assumption.
  (* <- *)
  intros.
  unfold not in *.
  unfold In in *.
  intros.
  inversion H.
  apply H1.
  inversion H0.
  assumption.
  apply H1.
  inversion H0.
  assumption.
Qed.

Hint Resolve not_in_intersect : ensemble.

Lemma not_in_union : forall X x s1 s2,
  ~ In X (Union X s1 s2) x <-> ~ In X s1 x /\ ~ In X s2 x.
Proof.
  intros.
  split.
  (*->*)
  intros.
  split.
  unfold In in *.
  unfold not in *.
  intros.
  apply H.
  apply Union_introl.
  assumption.
  unfold not in *.
  intros.
  apply H.
  apply Union_intror.
  assumption.
  (*<-*)
  intros [Hleft Hright].
  unfold not in *.
  unfold In in *.
  intros.
  inversion H.
  apply Hleft.
  apply H0.
  apply Hright. 
  apply H0.
Qed.

Hint Resolve not_in_union : ensemble.

Ltac invert_all :=
  match goal with
    | [ H1 : In _ (Union _ _ _) _ |- ?goal ] => 
                    inversion H1; subst; clear H1; invert_all
    | [ H1 : In _ (Setminus _ _ _) _ |- ?goal ] => 
                    inversion H1; subst; clear H1; invert_all
    | [ H1 : ~In _ (Union _ _ _) _ |- ?goal ] => 
                    apply not_in_union in H1; invert_all
    | [ H1 : ~In _ (Intersection _ _ _) _ |- ?goal ] => 
                    apply not_in_intersect in H1; invert_all
    | [ H1 : _ /\ _ |- ?goal ] => 
                    inversion H1; subst; clear H1; invert_all
    | [ H1 : _ \/ _ |- ?goal ] => 
                    inversion H1; subst; clear H1; invert_all
    | _ => idtac
  end.

Tactic Notation "set_eq" :=
  apply Extensionality_Ensembles;
  split; intros w Hi;
  invert_all;
  try solve by inversion;
  auto 10 with sets ensemble.


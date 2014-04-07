Require Export WLImp.
Require Export WLHoare.
Require Export Coq.Sets.Ensembles.
Require Export Util.

(** Definition of bug and correct program *)
Inductive no_bug: Assertion := 
  | No_Bug: no_bug empty_wlstate. 

Definition correct_program (c: com) : Prop :=
  {{ no_bug }} c {{ no_bug }}.

Definition wl_set : Type := Ensemble wakelock.
Definition wl_empty_set : wl_set := Empty_set wakelock.

(** Reaching definition analysis *)
Inductive kill : com -> wl_set -> Prop := 
  | K_SKIP : kill SKIP wl_empty_set
  | K_Acq : forall wl,
      kill (ACQ wl) wl_empty_set
  | K_Rel : forall wl,
      kill (REL wl) (Add wakelock wl_empty_set wl)
  | K_Seq : forall c1 c2 wls wls',
      kill c1 wls ->
      kill c2 wls' ->
      kill (c1 ;; c2) (Union wakelock wls wls')
  | K_If : forall b c1 c2 wls wls',
      kill c1 wls ->
      kill c2 wls' ->
      kill (IFB b THEN c1 ELSE c2 FI) (Intersection wakelock wls wls')
  | K_While : forall b c, kill (WHILE b DO c END) wl_empty_set.

Example test_kill_1 :
  kill ((ACQ WL0);;
     IFB BIsHeld WL0
       THEN REL WL0
       ELSE SKIP
     FI) wl_empty_set.
Proof.
  replace wl_empty_set with (Union wakelock wl_empty_set wl_empty_set).
  apply K_Seq. constructor.
  replace wl_empty_set with 
    (Intersection wakelock (Add wakelock wl_empty_set WL0) wl_empty_set).
  apply K_If. apply K_Rel. apply K_SKIP.
  
  apply empty_intersect. apply empty_union.
Qed.

Example test_kill_2 :
  kill ((ACQ WL0);;(REL WL0)) (Add wakelock wl_empty_set WL0).
Proof.
  replace (Add wakelock wl_empty_set WL0) 
      with (Union wakelock wl_empty_set (Add wakelock wl_empty_set WL0)).
  apply K_Seq. 
  apply K_Acq.
  apply K_Rel.
  apply empty_S_union.
Qed.      

Inductive gen : com -> wl_set -> Prop := 
  | G_SKIP : gen SKIP wl_empty_set
  | G_Acq : forall wl,
      gen (ACQ wl) (Add wakelock wl_empty_set wl)
  | G_Rel : forall wl,
      gen (REL wl) wl_empty_set
  | G_Seq : forall c1 c2 wls wls',
      gen c1 wls ->
      gen c2 wls' ->
      gen (c1 ;; c2) (Union wakelock wls wls')
  | G_If : forall b c1 c2 wls wls',
      gen c1 wls ->
      gen c2 wls' ->
      gen (IFB b THEN c1 ELSE c2 FI) (Union wakelock wls wls')
  | G_While : forall b c wls, 
      gen c wls -> gen (WHILE b DO c END) wls.

Example test_gen_1 :
  gen ((ACQ WL0);;
     IFB BIsHeld WL0
       THEN REL WL0
       ELSE SKIP
     FI) (Add wakelock wl_empty_set WL0).
Proof.
  replace (Add wakelock wl_empty_set WL0) 
      with (Union wakelock (Add wakelock wl_empty_set WL0) wl_empty_set).
  apply G_Seq. constructor.
  replace wl_empty_set with 
    (Union wakelock wl_empty_set wl_empty_set).
  apply G_If. apply G_Rel. apply G_SKIP.
  
  apply empty_union. rewrite union_commute. apply empty_S_union.
Qed.

Example test_gen_2 :
  gen (((ACQ WL0);;(REL WL0))) (Add wakelock wl_empty_set WL0).
Proof.
  replace (Add wakelock wl_empty_set WL0) with (Union wakelock (Add wakelock wl_empty_set WL0) (wl_empty_set)).
  apply G_Seq.
  apply G_Acq.
  apply G_Rel.
  rewrite union_commute.
  apply empty_S_union.
Qed.
  


Inductive flow : wl_set -> com -> wl_set -> Prop :=
    | FLOW : forall inB c kB gB, 
               kill c kB -> 
               gen c gB -> 
               flow inB c (Union wakelock (Setminus wakelock inB kB) gB).

Notation "<< P >>  c  << Q >>" :=
  (flow P c Q) (at level 90, c at next level).

Example test_flow_1 :
  << wl_empty_set >>
      ((ACQ WL0);;
     IFB BIsHeld WL0
       THEN REL WL0
       ELSE SKIP
     FI)
  << (Add wakelock wl_empty_set WL0) >>.
Proof. 
  replace (Add wakelock wl_empty_set WL0) 
    with (Union wakelock (Setminus wakelock wl_empty_set wl_empty_set) (Add wakelock wl_empty_set WL0)).
  apply FLOW. 
  apply test_kill_1. 
  apply test_gen_1. 
  rewrite empty_minus. rewrite empty_S_union. reflexivity.
Qed.

Example test_flow_2 :
  << wl_empty_set >>
      ((ACQ WL0);;(REL WL0))
  << (Add wakelock wl_empty_set WL0)>>.
Proof.
  replace (Add wakelock wl_empty_set WL0) with 
  (Union wakelock (Setminus wakelock wl_empty_set (Add wakelock wl_empty_set WL0)) ((Add wakelock wl_empty_set WL0))).
  apply FLOW.
  apply test_kill_2.
  apply test_gen_2.
  rewrite empty_minus_S. rewrite empty_S_union. reflexivity.
Qed.
  
  
  

Theorem flow_no_bug : forall c,
  ~ (<< wl_empty_set >> c << wl_empty_set >>) ->
  ~ (correct_program c).
  
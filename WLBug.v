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

Inductive single_stmt : com -> Prop :=
  | SS_Skip : single_stmt SKIP
  | SS_Acq : forall wl, single_stmt (ACQ wl)
  | SS_Rel : forall wl, single_stmt (REL wl).

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

Theorem flow_no_bug : forall c,
  ~ (<< wl_empty_set >> c << wl_empty_set >>) ->
  ~ (correct_program c).
  
(** * Hoare: Hoare Logic, Part I *)

Require Export WLImp.

(* ####################################################### *)
(** * Hoare Logic *)

(** Hoare Logic combines two beautiful ideas: a natural way of
    writing down _specifications_ of programs, and a _compositional
    proof technique_ for proving that programs are correct with
    respect to such specifications -- where by "compositional" we mean
    that the structure of proofs directly mirrors the structure of the
    programs that they are about. *)

(* ####################################################### *)
(** ** Assertions *)

(** To talk about specifications of programs, the first thing we
    need is a way of making _assertions_ about properties that hold at
    particular points during a program's execution -- i.e., claims
    about the current state of the memory when program execution
    reaches that point.  Formally, an assertion is just a family of
    propositions indexed by a [state]. *)

Definition Assertion := wlstate -> Prop.

(** This way of writing assertions can be a little bit heavy,
    for two reasons: (1) every single assertion that we ever write is
    going to begin with [fun st => ]; and (2) this state [st] is the
    only one that we ever use to look up variables (we will never need
    to talk about two different memory states at the same time).  For
    discussing examples informally, we'll adopt some simplifying
    conventions: we'll drop the initial [fun st =>], and we'll write
    just [X] to mean [st X].  Thus, instead of writing *)
(** 
      fun st => (st Z) * (st Z) <= m /\
                ~ ((S (st Z)) * (S (st Z)) <= m)
    we'll write just
         Z * Z <= m /\ ~((S Z) * (S Z) <= m).
*)

(** Given two assertions [P] and [Q], we say that [P] _implies_ [Q],
    written [P ->> Q] (in ASCII, [P -][>][> Q]), if, whenever [P]
    holds in some state [st], [Q] also holds. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** We'll also have occasion to use the "iff" variant of implication
    between assertions: *)

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* ####################################################### *)
(** ** Hoare Triples *)

(** Next, we need a way of making formal claims about the
    behavior of commands. *)

(** Since the behavior of a command is to transform one state to
    another, it is natural to express claims about commands in terms
    of assertions that are true before and after the command executes:

      - "If command [c] is started in a state satisfying assertion
        [P], and if [c] eventually terminates in some final state,
        then this final state will satisfy the assertion [Q]."

    Such a claim is called a _Hoare Triple_.  The property [P] is
    called the _precondition_ of [c], while [Q] is the
    _postcondition_.  Formally: *)

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st'  ->
       P st  ->
       Q st'.

(** Since we'll be working a lot with Hoare triples, it's useful to
    have a compact notation:
       {{P}} c {{Q}}.
*)
(** (The traditional notation is [{P} c {Q}], but single braces
    are already used for other things in Coq.)  *)

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.


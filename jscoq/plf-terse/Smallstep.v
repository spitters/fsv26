(** * Smallstep: Small-step Operational Semantics *)

Set Warnings "-notation-overridden".
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.

Definition FILL_IN_HERE := <{True}>.

(* ================================================================= *)
(** ** Big-step Evaluation

    Our semantics for Imp is written in the so-called
    "big-step" style...

    Evaluation rules take an expression (or command) to a final answer
    "all in one step":

      2 + 2 + 3 * 4 ==> 16

  But big-step semantics makes it hard to talk about what
  happens _along the way_...
*)

(* ================================================================= *)
(** ** Small-step Evaluation

    _Small-step_ style: Alternatively, we can show how to "reduce"
    an expression to a simpler form by performing a single step
    of computation:

      2 + 2 + 3 * 4
      --> 2 + 2 + 12
      --> 4 + 12
      --> 16

    Advantages of the small-step style include:

        - Finer-grained "abstract machine", closer to real
          implementations

        - Extends smoothly to concurrent languages and languages
          with other sorts of _computational effects_.

        - Separates _divergence_ (nontermination) from
          _stuckness_ (run-time error)

*)

(* ################################################################# *)
(** * A Toy Language *)

(** The world's simplest programming language: *)

Inductive tm : Type :=
  | C : nat -> tm         (* Constant *)
  | P : tm -> tm -> tm.   (* Plus *)

(* ----------------------------------------------------------------- *)
(** *** Big-step evaluation as a function *)

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P t1 t2 => evalF t1 + evalF t2
  end.

(* ----------------------------------------------------------------- *)
(** *** Big-step evaluation as a relation

                               ---------                               (E_C)
                               C n ==> n

                               t1 ==> n1
                               t2 ==> n2
                           -------------------                         (E_P)
                           P t1 t2 ==> n1 + n2
*)

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
  | E_C : forall n,
      C n ==> n
  | E_P : forall t1 t2 n1 n2,
      t1 ==> n1 ->
      t2 ==> n2 ->
      P t1 t2 ==> (n1 + n2)

where " t '==>' n " := (eval t n).

Module SimpleArith1.

(* ----------------------------------------------------------------- *)
(** *** Small-step evaluation relation

                     -------------------------------                (ST_PCC)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_P1)
                         P t1 t2 --> P t1' t2

                              t2 --> t2'
                      ----------------------------                   (ST_P2)
                      P (C n1) t2 --> P (C n1) t2'
*)
(** Notice:

       - each step reduces the _leftmost_ [P] node that is ready to go

             - first rule tells how to rewrite this node

             - second and third rules tell where to find it

       - constants are not related to anything -- i.e., they do not step
         to anything
*)
(* ----------------------------------------------------------------- *)
(** *** Small-step evaluation in Rocq *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'

  where " t '-->' t' " := (step t t').

(* ----------------------------------------------------------------- *)
(** *** Examples *)

(** If [t1] can take a step to [t1'], then [P t1 t2] steps
    to [P t1' t2]: *)

Example test_step_1 :
      P
        (P (C 1) (C 3))
        (P (C 2) (C 4))
      -->
      P
        (C 4)
        (P (C 2) (C 4)).
Proof.
  apply ST_P1. apply ST_PCC.  Qed.

(* QUIZ

    To what does the following term step?

    P (P (C 1) (C 2)) (P (C 1) (C 2))

    (A) [C 6]

    (B) [P (C 3) (P (C 1) (C 2))]

    (C) [P (P (C 1) (C 2)) (C 3)]

    (D) [P (C 3) (C 3)]

    (E) None of the above

_________________________________________________
Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'
*)
(* QUIZ

    What about this one?

    C 1

    (A) [C 1]

    (B) [P (C 0) (C 1)]

    (C) None of the above

_________________________________________________
Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall n1 t2 t2',
      t2 --> t2' ->
      P (C n1) t2 --> P (C n1) t2'
*)

End SimpleArith1.

(* ################################################################# *)
(** * Relations *)

(** A _binary relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition about
    pairs of elements of [X].  *)

Definition relation (X : Type) := X -> X -> Prop.

(** The step relation [-->] is an example of a relation on [tm]. *)

(* ----------------------------------------------------------------- *)
(** *** Determinism *)

(** One simple property of the [-->] relation is that, like the
    big-step evaluation relation for Imp, it is _deterministic_.

    _Theorem_: For each [t], there is at most one [t'] such that [t]
    steps to [t'] ([t --> t'] is provable). *)

(** Formally: *)

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Module SimpleArith2.
Import SimpleArith1.

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic. intros x y1 y2 Hy1.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - (* ST_PCC *) inversion Hy2; subst.
    + (* ST_PCC *) reflexivity.
    + (* ST_P1 *) inversion H2.
    + (* ST_P2 *) inversion H2.
  - (* ST_P1 *) inversion Hy2; subst.
    + (* ST_PCC *)
      inversion Hy1.
    + (* ST_P1 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
    + (* ST_P2 *)
      inversion Hy1.
  - (* ST_P2 *) inversion Hy2; subst.
    + (* ST_PCC *)
      inversion Hy1.
    + (* ST_P1 *) inversion H2.
    + (* ST_P2 *)
      apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith2.

(** Automation digression...

    Let's define a little tactic to decrease annoying repetition in
    this proof: *)

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

(** The proof of the previous theorem can now be simplified... *)

Module SimpleArith3.
Import SimpleArith1.

Theorem step_deterministic_alt: deterministic step.
Proof.
  intros x y1 y2 Hy1.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try solve_by_invert.
  - (* ST_PCC *) reflexivity.
  - (* ST_P1 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
  - (* ST_P2 *)
    apply IHHy1 in H2. rewrite H2. reflexivity.
Qed.

End SimpleArith3.

(* ================================================================= *)
(** ** Values *)

(** It can be useful to think of the [-->] relation as defining an
    _abstract machine_:

      - At any moment, the _state_ of the machine is a term.

      - A _step_ of the machine is an atomic unit of computation --
        here, a single "add" operation.

      - The _halting states_ of the machine are ones where there is no
        more computation to be done.

    We can then _execute_ a term [t] as follows:

      - Take [t] as the starting state of the machine.

      - Repeatedly use the [-->] relation to find a sequence of
        machine states, starting with [t], where each state steps to
        the next.

      - When no more reduction is possible, "read out" the final state
        of the machine as the result of execution. *)

(** Final states of our machine are terms of the form
    [C n] for some [n].  We call such terms _values_. *)

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n).

(** This gives a more elegant way of writing the [ST_P2] rule:

                     -------------------------------                (ST_PCC)
                     P (C n1) (C n2) --> C (n1 + n2)

                              t1 --> t1'
                         --------------------                        (ST_P1)
                         P t1 t2 --> P t1' t2

                               value v1
                              t2 --> t2'
                         --------------------                        (ST_P2)
                         P v1 t2 --> P v1 t2'
*)

(** Again, variable names carry important information:
       - [v1] ranges only over values
       - [t1] and [t2] range over arbitrary terms

    So the [value] hypothesis in the last rule is actually redundant
    in the informal presentation: The naming convention tells us where
    to add it when translating the informal rule to Rocq.  We'll keep
    it for now, but in later chapters we'll elide it. *)

(**  Here are the formal rules: *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
          P (C n1) (C n2)
      --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
        t1 --> t1' ->
        P t1 t2 --> P t1' t2
  | ST_P2 : forall v1 t2 t2',
        value v1 ->                     (* <--- n.b. *)
        t2 --> t2' ->
        P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

(* ================================================================= *)
(** ** Strong Progress and Normal Forms *)

(** _Theorem_ (_Strong Progress_): If [t] is a term, then either [t]
    is a value or else there exists a term [t'] such that [t --> t']. *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t --> t').
Proof.
  induction t.
  - (* C case *) left. apply v_C.
  - (* P case *) right. destruct IHt1 as [IHt1 | [t1' Ht1] ].
    + (* t1 is a value *) destruct IHt2 as [IHt2 | [t2' Ht2] ].
      * (* t2 is a value *) inversion IHt1. inversion IHt2.
        exists (C (n + n0)).
        apply ST_PCC.
      * (* t2 steps *)
        exists (P t1 t2').
        apply ST_P2; auto.
    + (* t1 steps *)
      exists (P t1' t2).
      apply ST_P1. apply Ht1.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Normal forms *)

(** The idea of "making progress" can be extended to tell us something
    interesting about values in this language: they are exactly the
    terms that do _not_ make progress in this sense.

    To state this observation formally, let's begin by giving a name
    to "terms that cannot make progress."  We'll call them _normal
    forms_.  *)

Definition normal_form {X : Type}
              (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

(* ----------------------------------------------------------------- *)
(** *** Values vs. Normal Forms *)

(* QUIZ

    What is a _value_ in this language?

    What is a _normal form_?
*)

(** In this language, normal forms and values coincide: *)

Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. intros v H contra.
  destruct contra. destruct H. inversion H0.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t --> t').
  { apply strong_progress. }
  destruct G as [G | G].
  - (* l *) apply G.
  - (* r *) contradiction.
Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split.
  - apply nf_is_value.
  - apply value_is_nf.
Qed.

(** Why is this interesting?

    Because [value] is a syntactic concept -- it is defined by looking
    at the way a term is written -- while [normal_form] is a semantic
    one -- it is defined by looking at how the term steps.

    It is not obvious that these concepts should characterize the same
    set of terms!  *)

(** Indeed, we could easily have written the definitions (incorrectly)
    so that they would _not_ coincide... *)

(** We might, for example, define [value] so that it
    includes some terms that are not finished reducing: *)

Module Temp1.

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n)
  | v_funny : forall t1 n,
                value (P t1 (C n)).              (* <--- *)

Reserved Notation " t '-->' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').
(* QUIZ

    Using this wrong definition of [value], to how many different values
    does the following term reduce in zero or more steps?

       P
         (P (C 1) (C 2))
         (C 3)

  ________________________________________
      Inductive value : tm -> Prop :=
        | v_C : forall n, value (C n)
        | v_funny : forall t1 n,
                      value (P t1 (C n)).

*)

(* QUIZ

    To how many different terms does the following term [step]
    (in one step)?

       P (P (C 1) (C 2)) (P (C 3) (C 4))

  ________________________________________
      Inductive value : tm -> Prop :=
        | v_C : forall n, value (C n)
        | v_funny : forall t1 n,
                      value (P t1 (C n)).
*)

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  (* FILL IN HERE *) Admitted.
End Temp1.

(** Or we might (again, wrongly) define [step] so that it permits
    something designated as a value to reduce further. *)

Module Temp2.

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n).         (* Original definition *)

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n,
      C n --> P (C n) (C 0)                  (* <--- NEW *)
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2
  | ST_P2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      P v1 t2 --> P v1 t2'

  where " t '-->' t' " := (step t t').

(* QUIZ

    With this definition, to how many different terms does
    the following term step (in exactly one step)?

      P (C 1) (C 3)

   _______________________________________
     Inductive step : tm -> tm -> Prop :=
       | ST_Funny : forall n,
           C n --> P (C n) (C 0)
       | ST_PCC : forall n1 n2,
           P (C n1) (C n2) --> C (n1 + n2)
       | ST_P1 : forall t1 t1' t2,
           t1 --> t1' ->
           P t1 t2 --> P t1' t2
       | ST_P2 : forall v1 t2 t2',
           value v1 ->
           t2 --> t2' ->
           P v1 t2 --> P v1 t2'

*)
(* /QUIZ

    And we again lose the property that values are the same as
    normal forms: *)

Lemma value_not_same_as_normal_form :
  exists v, value v /\ ~ normal_form step v.
Proof.
  (* FILL IN HERE *) Admitted.

End Temp2.

(** Finally, we might define [value] and [step] so that there is some
    term that is _not_ a value but that _also_ cannot take a step.

    Such terms are said to be _stuck_. *)

Module Temp3.

Inductive value : tm -> Prop :=
  | v_C : forall n, value (C n).

Reserved Notation " t '-->' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_PCC : forall n1 n2,
      P (C n1) (C n2) --> C (n1 + n2)
  | ST_P1 : forall t1 t1' t2,
      t1 --> t1' ->
      P t1 t2 --> P t1' t2

  where " t '-->' t' " := (step t t').

(** (Note that [ST_P2] is missing.) *)

(* QUIZ

    With this definition, to how many terms does the
    following term step (in one step)?

    P (C 1) (P (C 1) (C 2))

  _________________________________________
    Inductive step : tm -> tm -> Prop :=
      | ST_PCC : forall n1 n2,
          P (C n1) (C n2) --> C (n1 + n2)
      | ST_P1 : forall t1 t1' t2,
          t1 --> t1' ->
          P t1 t2 --> P t1' t2
*)

(** And, once again: *)

Lemma value_not_same_as_normal_form :
  exists t, ~ value t /\ normal_form step t.
Proof.
  (* FILL IN HERE *) Admitted.

End Temp3.

(* ################################################################# *)
(** * Multi-Step Reduction *)

(** We can now use the single-step relation and the concept of value
    to formalize an entire _execution_ of the abstract machine.

    First, we define a _multi-step reduction relation_ [-->*] that
    relates a starting term to _every_ term that it can reach by
    some number of reduction steps (including zero). *)

(** Since we'll want to reuse the idea of multi-step reduction many
    times with many different single-step relations, let's pause and
    define the concept generically.

    Given a relation [R] (e.g., the step relation [-->]), we define a
    new relation [multi R], called the _multi-step closure of [R]_ as
    follows. *)

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

(** The effect of this definition is that [multi R] relates two
    elements [x] and [y] if

       - [x = y], or
       - [R x y], or
       - there is some nonempty sequence [z1], [z2], ..., [zn] such that

           R x z1
           R z1 z2
           ...
           R zn y.

    Intuitively, if [R] describes a single-step of computation, then
    [z1] ... [zn] are the intermediate steps of computation that get
    us from [x] to [y]. *)

(** We write [-->*] for the [multi step] relation on terms. *)

Notation " t '-->*' t' " := (multi step t t') (at level 40).

(** The relation [multi R] has several crucial properties.

    First, it is obviously _reflexive_ (that is, [forall x, multi R x
    x]).  In the case of the [-->*] (i.e., [multi step]) relation, the
    intuition is that a term can execute to itself by taking zero
    steps of reduction. *)

(** Second, it contains [R] -- that is, single-step reductions are a
    particular case of multi-step executions.  (It is this fact that
    justifies the word "closure" in the term "multi-step closure of
    [R].") *)

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y.
  - apply H.
  - apply multi_refl.
Qed.

(** Third, [multi R] is _transitive_. *)

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y.
      + assumption.
      + apply IHG. assumption.
Qed.

(** In particular, for the [multi step] relation on terms, if
    [t1 -->* t2] and [t2 -->* t3], then [t1 -->* t3]. *)

(* QUIZ

    Which of the following relations on numbers _cannot_ be expressed
    as [multi R] for some [R]?

    (A) less than or equal

    (B) strictly less than

    (C) equal

    (D) none of the above
*)

(** Here's a specific instance of the [multi step] relation: *)

Lemma test_multistep_1:
      P
        (P (C 0) (C 3))
        (P (C 2) (C 4))
   -->*
      C ((0 + 3) + (2 + 4)).
Proof.
  apply multi_step with
            (P (C (0 + 3))
               (P (C 2) (C 4))).
  { apply ST_P1. apply ST_PCC. }
  apply multi_step with
            (P (C (0 + 3))
               (C (2 + 4))).
  { apply ST_P2.
    - apply v_C.
    - apply ST_PCC. }
  apply multi_R.
  apply ST_PCC.
Qed.

(* ================================================================= *)
(** ** Normal Forms Again *)

(** If [t] reduces to [t'] in zero or more steps and [t'] is a
    normal form, we say that "[t'] is a normal form of [t]." *)

Definition normal_form_of {X : Type} (R : relation X)  (t t' : X) :=
  ((multi R) t t' /\ normal_form R t').

(** Notice:

      - single-step reduction is deterministic;

      - so, if [t] can reach a normal form, then this normal form is unique;

      - so we can pronounce [normal_form t t'] as "[t'] is _the_
        normal form of [t]." *)

(** **** Exercise: 3 stars, standard, optional (normal_forms_unique) *)
Theorem normal_forms_unique:
  deterministic (normal_form_of step).
Proof.
  (* We recommend using this initial setup as-is! *)
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12].
  destruct P2 as [P21 P22].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Indeed, something stronger is true for this language:

       - the reduction of _any_ term [t] will eventually reach a
         normal form in a finite number of steps

    We say the [step] relation is _normalizing_. *)

Definition normalizing {X : Type} (R : relation X) :=
  forall t, exists t', normal_form_of R t t'.

(** To prove that [step] is normalizing, we need a couple of lemmas. *)

Lemma multistep_congr_1 : forall t1 t1' t2,
     t1 -->* t1' ->
     P t1 t2 -->* P t1' t2.
Proof.
  intros t1 t1' t2 H. induction H.
  - (* multi_refl *) apply multi_refl.
  - (* multi_step *) apply multi_step with (P y t2).
    + apply ST_P1. apply H.
    + apply IHmulti.
Qed.

Lemma multistep_congr_2 : forall v1 t2 t2',
     value v1 ->
     t2 -->* t2' ->
     P v1 t2 -->* P v1 t2'.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  induction t.
  - (* C case *)
    exists (C n).
    split.
    + (* l *) apply multi_refl.
    + (* r *)
      (* We can use [rewrite] with "iff" statements, not
           just equalities: *)
      apply nf_same_as_value. apply v_C.

  - (* P case *)
    destruct IHt1 as [t1' [Hsteps1 Hnormal1] ].
    destruct IHt2 as [t2' [Hsteps2 Hnormal2] ].
    apply nf_same_as_value in Hnormal1.
    apply nf_same_as_value in Hnormal2.
    destruct Hnormal1 as [n1].
    destruct Hnormal2 as [n2].
    exists (C (n1 + n2)).
    split.
    + (* l *)
      apply multi_trans with (P (C n1) t2).
      * apply multistep_congr_1. apply Hsteps1.
      * apply multi_trans with (P (C n1) (C n2)).
        { apply multistep_congr_2.
          - apply v_C.
          - apply Hsteps2. }
        apply multi_R. apply ST_PCC.
    + (* r *)
      apply nf_same_as_value. apply v_C.
Qed.

(* ================================================================= *)
(** ** Equivalence of Big-Step and Small-Step *)

(** Having defined the operational semantics of our tiny programming
    language in two different ways (big-step and small-step), it makes
    sense to ask whether these definitions actually define the same
    thing! *)

(** We consider the two implications separately. *)

Theorem eval__multistep : forall t n,
  t ==> n -> t -->* C n.

(** The key ideas in the proof can be seen in the following picture:

       P t1 t2 -->            (by ST_P1)
       P t1' t2 -->           (by ST_P1)
       P t1'' t2 -->          (by ST_P1)
       ...
       P (C n1) t2 -->        (by ST_P2)
       P (C n1) t2' -->       (by ST_P2)
       P (C n1) t2'' -->      (by ST_P2)
       ...
       P (C n1) (C n2) -->    (by ST_PCC)
       C (n1 + n2)

    That is, the multi-step reduction of a term of the form [P t1 t2]
    proceeds in three phases:
       - First, we use [ST_P1] some number of times to reduce [t1]
         to a normal form, which must (by [nf_same_as_value]) be a
         term of the form [C n1] for some [n1].
       - Next, we use [ST_P2] some number of times to reduce [t2]
         to a normal form, which must again be a term of the form [C
         n2] for some [n2].
       - Finally, we use [ST_PCC] one time to reduce [P (C
         n1) (C n2)] to [C (n1 + n2)]. *)

Proof.
  (* FILL IN HERE *) Admitted.

(** For the other direction, we need one lemma, which establishes a
    relation between single-step reduction and big-step evaluation. *)

Lemma step__eval : forall t t' n,
     t --> t' ->
     t' ==> n ->
     t  ==> n.
Proof.
  intros t t' n Hs. generalize dependent n.
  (* FILL IN HERE *) Admitted.

(** The fact that small-step reduction implies big-step evaluation is now
    straightforward to prove.

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)

Theorem multistep__eval : forall t t',
  normal_form_of step t t' -> exists n, t' = C n /\ t ==> n.
Proof.
  (* FILL IN HERE *) Admitted.

(* ################################################################# *)
(** * Small-Step Imp *)

(** Now for a more serious example: a small-step version of the Imp
    operational semantics. *)

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

(* ----------------------------------------------------------------- *)
(** *** Small-step evaluation relation for arithmetic expressions *)

(**[[[
                             ---------------------                     (AS_Id)
                             i / st --> ANum (st i)

                              a1 / st --> a1'
                         -------------------------                   (AS_P1)
                         a1 + a2 / st --> a1' + a2

                        aval v1       a2 / st --> a2'
                    -------------------------------------            (AS_P2)
                          v1 + a2 / st --> v1 + a2'

                        -------------------------------               (AS_P)
                        v1 + v2 / st --> ANum (v1 + v2)

                              a1 / st --> a1'
                          -------------------------                 (AS_Minus1)
                          a1 - a2 / st --> a1' - a2

                        aval v1       a2 / st --> a2'
                        ----------------------------                (AS_Minus2)
                           v1 - a2 / st --> v1 - a2'

                        -------------------------------              (AS_Minus)
                        v1 - v2 / st --> ANum (v1 - v2)

                              a1 / st --> a1'
                          -------------------------                  (AS_Mult1)
                          a1 * a2 / st --> a1' * a2

                        aval v1       a2 / st --> a2'
                        ----------------------------                 (AS_Mult2)
                           v1 * a2 / st --> v1 * a2'

                        -------------------------------               (AS_Mult)
                        v1 * v2 / st --> ANum (v1 * v2)
*)

Reserved Notation " a '/' st '-->a' a' "
                  (at level 40, st at next level, left associativity).
Inductive astep (st : state) : aexp -> aexp -> Prop :=
  | AS_Id : forall (i : string),
      i / st -->a ANum (st i)
  | AS_P1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 + a2 }> / st -->a <{ a1' + a2 }>
  | AS_P2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 + a2 }>  / st -->a <{ v1 + a2' }>
  | AS_P : forall (v1 v2 : nat),
      <{ v1 + v2 }> / st -->a ANum (v1 + v2)
  | AS_Minus1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 - a2 }> / st -->a <{ a1' - a2 }>
  | AS_Minus2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 - a2 }>  / st -->a <{ v1 - a2' }>
  | AS_Minus : forall (v1 v2 : nat),
      <{ v1 - v2 }> / st -->a ANum (v1 - v2)
  | AS_Mult1 : forall a1 a1' a2,
      a1 / st -->a a1' ->
      <{ a1 * a2 }> / st -->a <{ a1' * a2 }>
  | AS_Mult2 : forall v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      <{ v1 * a2 }>  / st -->a <{ v1 * a2' }>
  | AS_Mult : forall (v1 v2 : nat),
      <{ v1 * v2 }> / st -->a ANum (v1 * v2)

    where " a '/' st '-->a' a' " := (astep st a a').

(* ----------------------------------------------------------------- *)
(** *** Small-step evaluation relation for boolean expressions *)
(**[[[
                          a1 / st --> a1'
                     -------------------------                     (BS_Eq1)
                     a1 = a2 / st --> a1' = a2

                    aval v1       a2 / st --> a2'
                    -----------------------------                  (BS_Eq2)
                      v1 = a2 / st --> v1 = a2'

      -------------------------------------------------------      (BS_Eq)
      v1 = v2 / st --> (if (v1 =? v2) then BTrue else BFalse)

                            a1 / st --> a1'
                      ---------------------------                  (BS_LtEq1)
                      a1 <= a2 / st --> a1' <= a2

                    aval v1       a2 / st --> a2'
                   ------------------------------                  (BS_LtEq2)
                    v1 <= a2 / st --> v1 <= a2'

      ---------------------------------------------------------    (BS_LtEq)
      v1 <= v2 / st --> (if (v1 <=? v2) then BTrue else BFalse)

                           b1 / st --> b1'
                          -----------------                        (BS_NotStep)
                          ~b1 / st --> ~b1'

                        ---------------------                      (BS_NotTrue)
                        ~ true / st --> false

                        ---------------------                      (BS_NotFalse)
                        ~ false / st --> true

                            b1 / st --> b1'
                      ---------------------------                  (BS_AndStep)
                      b1 && b2 / st --> b1' && b2

                           b2 / st --> b2'
                    -------------------------------                (BS_AndTrueStep)
                    true && b2 / st --> true && b2'

                      --------------------------                   (BS_AndFalse)
                      false && b2 / st --> false

                      --------------------------                   (BS_AndTrueTrue)
                      true && true / st --> true

                     ----------------------------                  (BS_AndTrueFalse)
                     true && false / st --> false
*)
Reserved Notation " b '/' st '-->b' b' "
                  (at level 40, st at next level, left associativity).
Inductive bstep (st : state) : bexp -> bexp -> Prop :=
| BS_Eq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 = a2 }> / st -->b <{ a1' = a2 }>
| BS_Eq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 = a2 }> / st -->b <{ v1 = a2' }>
| BS_Eq : forall (v1 v2 : nat),
    <{ v1 = v2 }> / st -->b
    (if (v1 =? v2) then BTrue else BFalse)
| BS_LtEq1 : forall a1 a1' a2,
    a1 / st -->a a1' ->
    <{ a1 <= a2 }> / st -->b <{ a1' <= a2 }>
| BS_LtEq2 : forall v1 a2 a2',
    aval v1 ->
    a2 / st -->a a2' ->
    <{ v1 <= a2 }> / st -->b <{ v1 <= a2' }>
| BS_LtEq : forall (v1 v2 : nat),
    <{ v1 <= v2 }> / st -->b
    (if (v1 <=? v2) then BTrue else BFalse)
| BS_NotStep : forall b1 b1',
    b1 / st -->b b1' ->
    <{ ~ b1 }> / st -->b <{ ~ b1' }>
| BS_NotTrue  : <{ ~ true }> / st  -->b <{ false }>
| BS_NotFalse : <{ ~ false }> / st -->b <{ true }>
| BS_AndStep : forall b1 b1' b2,
    b1 / st -->b b1' ->
    <{ b1 && b2 }> / st -->b <{ b1' && b2 }>
| BS_AndTrueStep : forall b2 b2',
    b2 / st -->b b2' ->
    <{ true && b2 }> / st -->b <{ true && b2' }>
| BS_AndFalse : forall b2,
    <{ false && b2 }> / st -->b <{ false }>
| BS_AndTrueTrue  : <{ true && true  }> / st -->b <{ true }>
| BS_AndTrueFalse : <{ true && false }> / st -->b <{ false }>

where " b '/' st '-->b' b' " := (bstep st b b').

(** The semantics of commands is the interesting part.  We need two
    small tricks to make it work:

       - We use [skip] as a "command value" -- i.e., a command that
         has reached a normal form.

            - An assignment command reduces to [skip] (and an updated
              state).

            - The sequencing command waits until its left-hand
              subcommand has reduced to [skip], then throws it away so
              that reduction can continue with the right-hand
              subcommand.

       - We reduce a [while] command a single step by transforming it
         into a conditional followed by the same [while]. *)

(* ----------------------------------------------------------------- *)
(** *** Small-step evaluation relation for commands *)
(**[[[
                              a1 / st --> a1'
                     ------------------------------                           (CS_AsgnStep)
                     i := a1 / st --> i := a1' / st

                   --------------------------------------                     (CS_Asgn)
                   i := n / st --> skip / (i !-> n ; st)

                           c1 / st --> c1' / st'
                     -------------------------------                          (CS_SeqStep)
                     c1 ; c2 / st --> c1' ; c2 / st'

                        --------------------------                            (CS_SeqFinish)
                        skip ; c2 / st --> c2 / st

                              b1 / st --> b1'
               ---------------------------------------------------            (CS_IfStep)
               if b1 then c1 else c2 end / st -->
                                   if b1' then c1 else c2 end / st

              ---------------------------------------------                   (CS_IfTrue)
              if true then c1 else c2 end / st --> c1 / st

              ----------------------------------------------                  (CS_IfFalse)
              if false then c1 else c2 end / st --> c2 / st

              -----------------------------------------------------------------    (CS_While)
              while b1 do c1 end / st -->
                         if b1 then (c1; while b1 do c1 end) else skip end / st
*)

Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at next level, t' at next level, left associativity).
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

(* QUIZ

    The (small-step) semantics of Imp satisfies (1) / does not satisfy (2)
    the following properties (choose 1 for Yes, 2 for No):

      - determinism

      - strong progress (remember we use [skip] as a "command value")

      - values and normal forms coincide (i.e. there are no "stuck" terms)

      - the step relation is normalizing (i.e. Imp programs are terminating)
*)

(* ################################################################# *)
(** * Concurrent Imp *)

(** Finally, let's define a _concurrent_ extension of Imp, to
    show off the power of our new tools... *)

(** For example:
     - This program sets [X] to [0] in one thread and [1] in another,
       leaving it set to either [0] or [1] at the end:

          X := 0 || X := 1

     - This one leaves [X] set to one of [0], [1], [2], or [3] at the
       end:

          X := 0; (X := X+2 || X := X+1 || X := 0)
*)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.         (* <--- NEW: c1||c2 *)

Notation "x '||' y" := (CPar x y)
  (in custom com at level 100, right associativity,
    format "'[v'   x '/' '||' '/ '  y ']'").
Notation "'skip'"  := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgn x y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x  :=  y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99,
    format "'[v' 'if'  x  'then' '/  ' y '/' 'else' '/  ' z '/' 'end' ']'") : com_scope.
Notation "'while' x 'do' y 'end'" := (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99,
    format "'[v' 'while'  x  'do' '/  ' y '/' 'end' ']'") : com_scope.

(* ----------------------------------------------------------------- *)
(** *** New small-step evaluation relation for commands *)

(** Same rules as before, plus:

                           c1 / st --> c1' / st'
                     ---------------------------------                       (CS_Par1)
                     c1 || c2 / st --> c1' || c2 / st'

                           c2 / st --> c2' / st'
                     ---------------------------------                       (CS_Par2)
                     c1 || c2 / st --> c1 || c2' / st'

                     --------------------------------                        (CS_ParDone)
                     skip || skip / st --> skip / st
*)
Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part: *)
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      <{ c1 || c2 }> / st --> <{ c1' || c2 }> / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      <{ c1 || c2 }> / st --> <{ c1 || c2' }> / st'
  | CS_ParDone : forall st,
      <{ skip || skip }> / st --> <{ skip }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Notation " t '/' st '-->*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at next level, t' at next level, left associativity).

(* QUIZ

    Which state _cannot_ be obtained as a result of executing the
    following program (from any starting state)?

       (Y := 1 || Y := 2);
       X := Y

    (A) [Y=0] and [X=0]

    (B) [Y=1] and [X=1]

    (C) [Y=2] and [X=2]

    (D) None of the above

*)
(* QUIZ

    Which state(s) _cannot_ be obtained as a result of executing the
    following program (from any starting state)?

       (Y := 1 || Y := Y + 1);
       X := Y

    (A) [Y=1] and [X=1]

    (B) [Y=0] and [X=1]

    (C) [Y=2] and [X=2]

    (D) [Y=n] and [X=n] for any [n >= 3]

    (E) B and D above

    (6) None of the above

*)
(* QUIZ

    How about this one?

      ( Y := 0; X := Y + 1 )
   ||
      ( Y := Y + 1; X := 1 )

    (A) [Y=0] and [X=1]

    (B) [Y=1] and [X=1]

    (C) [Y=0] and [X=0]

    (D) [Y=4] and [X=1]

    (E) None of the above

*)
(* /QUIZ

    Among the many interesting properties of this language is the fact
    that the following program can terminate with the variable [X] set
    to any value. *)

Definition par_loop : com :=
  <{
      Y := 1
    ||
      while (Y = 0) do X := X + 1 end
   }>.

End CImp.

(* ################################################################# *)
(** * Aside: A [normalize] Tactic *)

(** Proofs that one expression multisteps to another can be
    tedious... *)

Example step_example1 :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  apply multi_step with (P (C 3) (C 7)).
  - apply ST_P2.
    + apply v_C.
    + apply ST_PCC.
  - apply multi_step with (C 10).
    + apply ST_PCC.
    + apply multi_refl.
Qed.

(** Proofs that one term normalizes to another must repeatedly apply
    [multi_step] until the term reaches a normal form.  Fortunately,
    the sub-proofs for the intermediate steps are simple enough that
    [auto], with appropriate hints, can solve them. *)

Hint Constructors step value : core.
Example step_example1' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  eapply multi_step; auto. simpl.
  eapply multi_step; auto. simpl.
  apply multi_refl.
Qed.

(** The following custom [Tactic Notation] definition captures this
    pattern.  In addition, before each step, we print out the current
    goal, so that we can follow how the term is being reduced. *)

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            [ (eauto 10; fail) | simpl]);
  apply multi_refl.

Example step_example1'' :
  (P (C 3) (P (C 3) (C 4)))
  -->* (C 10).
Proof.
  normalize.
  (* The [print_goal] in the [normalize] tactic shows
     a trace of how the expression reduced...
         (P (C 3) (P (C 3) (C 4)) -->* C 10)
         (P (C 3) (C 7) -->* C 10)
         (C 10 -->* C 10)
  *)
Qed.

(** The [normalize] tactic also provides a simple way to calculate the
    normal form of a term, by starting with a goal with an existentially
    bound variable. *)

Example step_example1''' : exists e',
  (P (C 3) (P (C 3) (C 4)))
  -->* e'.
Proof.
  eexists. normalize.
Qed.
(** This time, the trace is:

       (P (C 3) (P (C 3) (C 4)) -->* ?e')
       (P (C 3) (C 7) -->* ?e')
       (C 10 -->* ?e')

   where [?e'] is the variable ``guessed'' by eapply. *)


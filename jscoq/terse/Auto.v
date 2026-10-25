(** * Auto: More Automation *)

Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.String.
From LF Require Import Maps.
From LF Require Import Imp.

(** Consider the proof below, showing that [ceval] is
    deterministic.

    Notice all the repetition and near-repetition... *)

Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b evaluates to true *)
    apply IHE1. assumption.
  - (* b evaluates to false (contradiction) *)
    rewrite H in H5. discriminate.
  (* E_IfFalse *)
  - (* b evaluates to true (contradiction) *)
    rewrite H in H5. discriminate.
  - (* b evaluates to false *)
    apply IHE1. assumption.
  (* E_WhileFalse *)
  - (* b evaluates to false *)
    reflexivity.
  - (* b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * The [auto] Tactic *)

(** Thus far, our proof scripts mostly apply relevant hypotheses or
    lemmas by name, and only one at a time. *)

(** The [auto] tactic tries to free us from this drudgery by _searching_
    for a sequence of applications that will prove the goal: *)

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

(** The [auto] tactic solves goals that are solvable by any combination of
    [intros] and [apply]. *)

(** Here is a larger example showing [auto]'s power: *)

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

(** Proof search could, in principle, take an arbitrarily long time,
    so there is a limit to how deep [auto] will search by default. *)

(** If [auto] is not solving our goal as expected we can use [debug auto]
    to see a trace. *)
Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  (* When it cannot solve the goal, [auto] does nothing *)
  auto.

  (* Let's see where [auto] gets stuck using [debug auto] *)
  debug auto.

  (* Optional argument to [auto] says how deep to search
     (default is 5) *)
  auto 6.
Qed.

(** The [auto] tactic considers the hypotheses in the current
    context together with a _hint database_ of other lemmas and
    constructors.

    Some common facts about equality and logical operators are
    installed in the hint database by default. *)

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.

(** If we want to see which facts [auto] is using, we can use
    [info_auto] instead. *)

Example auto_example_5: 2 = 2.
Proof.
  info_auto.
Qed.

Example auto_example_5' : forall (P Q R S T U W: Prop),
  (U -> T) ->
  (W -> U) ->
  (R -> S) ->
  (S -> T) ->
  (P -> R) ->
  (U -> T) ->
  P ->
  T.
Proof.
  intros.
  info_auto.
Qed.

(** We can extend the hint database just for the purposes of one
    application of [auto] by writing "[auto using ...]". *)

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. lia. Qed.

Example auto_example_6 : forall n m p q : nat,
  (p = q -> (n <= m /\ m <= n)) ->
  p = q ->
  n = m.
Proof.
  auto using le_antisym.
Qed.

(** We can also _permanently_ extend the hint database:

      - [Hint Resolve T : core.]

        Add a theorem or constructor [T] to the global database

      - [Hint Constructors c : core.]

        Add _all_ constructors of [c] to the global database

      - [Hint Unfold d : core.]

        Automatically expand defined symbol [d] during [auto] *)

(** It is also possible to define specialized hint databases (besides
    [core]) that can be activated only when needed; indeed, it is good
    style to create your own hint databases instead of polluting
    [core].

    See the Rocq reference manual for details. *)

Hint Resolve le_antisym : core.

Example auto_example_6' : forall n m p q : nat,
  (p = q -> (n <= m /\ m <= n)) ->
  p = q ->
  n = m.
Proof.
  auto. (* picks up hint from database *)
Qed.

Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.  (* does nothing *)
Abort.

Hint Unfold is_fortytwo : core.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto. (* try also: info_auto. *)
Qed.

(** Let's take a first pass over [ceval_deterministic], using [auto]
    to simplify the proof script. *)

Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
    induction E1; intros st2 E2; inversion E2; subst;
    auto.             (* <---- here's one good place for auto *)
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.             (* <---- here's another *)
  - (* E_IfTrue *)
    rewrite H in H5. discriminate.
  - (* E_IfFalse *)
    rewrite H in H5. discriminate.
  - (* E_WhileFalse *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, with b false *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, with b true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto.             (* <---- and another *)
Qed.

(* ################################################################# *)
(** * Searching For Hypotheses *)

(** The proof has become simpler, but there is still an annoying
    amount of repetition.

    Let's first tackle the contradiction cases.  Each occurs where we
    have hypothesis of the form

      H1: beval st b = false

    as well as:

      H2: beval st b = true

    First step: abstracting out that piece as a script in Ltac. *)

Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.

(** Using [rwd]... *)

Theorem ceval_deterministic'': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - (* E_IfTrue *)
    rwd H H5.                 (* <----- *)
  - (* E_IfFalse *)
    rwd H H5.                 (* <----- *)
  - (* E_WhileFalse *)
    rwd H H2.                 (* <----- *)
  - (* E_WhileTrue - b false *)
    rwd H H4.                 (* <----- *)
  - (* EWhileTrue - b true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto. Qed.

(** That's a bit better, but we really want Rocq to discover the
    relevant hypotheses for us.  We can do this by using the [match
    goal] facility of Ltac. *)

Ltac find_rwd :=
  match goal with
    H1: ?E = true, H2: ?E = false |- _
       =>
    rwd H1 H2
  end.

(** The [match goal] tactic looks for hypotheses matching the
    pattern specified. In this case, we're looking for two equalities
    [H1] and [H2] equating the same expression [?E] to both [true] and
    [false]. *)

Theorem ceval_deterministic''': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst;
       try find_rwd;                                  (* <------ *)
       auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - (* E_WhileTrue - b true *)
    rewrite (IHE1_1 st'0 H3) in *.
    auto. Qed.

(** Let's see about the remaining cases. Each of them involves
    rewriting a hypothesis after feeding it with the required
    condition. We can automate the task of finding the relevant
    hypotheses to rewrite with. *)

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _
    => rewrite (H1 X H2) in *
  end.

(** Now we can make use of [find_eqn] to repeatedly rewrite
    with the appropriate hypothesis, wherever it may be found. *)

Theorem ceval_deterministic'''': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst;
    try find_rwd;
    try find_eqn;    (* <------- *)
    auto.
Qed.

(** The big payoff in this approach is that the new proof script is
    more robust in the face of changes to our language.  To test this,
    let's try adding a [REPEAT] command to the language. *)

Module Repeat.

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CRepeat (c : com) (b : bexp).

(** [REPEAT] behaves like [while], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Notation "'repeat' x 'until' y 'end'" :=
         (CRepeat x y)
            (in custom com at level 0,
             x at level 99, y at level 99).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_RepeatEnd : forall st st' b c,
      st  =[ c ]=> st' ->
      beval st' b = true ->
      st  =[ repeat c until b end ]=> st'
  | E_RepeatLoop : forall st st' st'' b c,
      st  =[ c ]=> st' ->
      beval st' b = false ->
      st' =[ repeat c until b end ]=> st'' ->
      st  =[ repeat c until b end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(** Our first attempt at the determinacy proof does not quite succeed:
    the [E_RepeatEnd] and [E_RepeatLoop] cases are not handled by our
    previous automation. *)

Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inversion E2; subst; try find_rwd; try find_eqn; auto.
  - (* E_RepeatEnd *)
    + (* b evaluates to false (contradiction) *)
       find_rwd.
       (* oops: why didn't [find_rwd] solve this for us already?
          answer: we did things in the wrong order. *)
  - (* E_RepeatLoop *)
     + (* b evaluates to true (contradiction) *)
        find_rwd.
Qed.

(** Fortunately, to fix this, we just have to swap the invocations of
    [find_eqn] and [find_rwd]. *)

Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inversion E2; subst; try find_eqn; try find_rwd; auto.
Qed.

End Repeat.

(* ################################################################# *)
(** * The [eapply] and [eauto] tactics *)

(** Recall this example from the [Imp] chapter: *)

Example ceval_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We supply the intermediate state [st']... *)
  apply E_Seq with (X !-> 2).
  - apply E_Asgn. reflexivity.
  - apply E_IfFalse. reflexivity. apply E_Asgn. reflexivity.
Qed.

(** In the first step of the proof, we had to explicitly provide
    the intermediate state [X !-> 2], due to the "hidden" argument [st']
    to the [E_Seq] constructor:

          E_Seq : forall c1 c2 st st' st'',
            st  =[ c1 ]=> st'  ->
            st' =[ c2 ]=> st'' ->
            st  =[ c1 ; c2 ]=> st''
*)

(** If we leave out the [with], this step fails, because Rocq
    cannot find an instance for the variable [st']. But this is silly,
    since the appropriate value for [st'] will become obvious in the
    very next step. *)

(** With [eapply], we can eliminate this silliness: *)

Example ceval'_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* 1 *) eapply E_Seq.
  - (* 2 *) apply E_Asgn.
    (* 3 *) reflexivity.
  - (* 4 *) apply E_IfFalse. reflexivity. apply E_Asgn. reflexivity.
Qed.

(** Several of the tactics that we've seen so far, including [exists],
    [constructor], and [auto], have similar variants. The [eauto]
    tactic works like [auto], except that it uses [eapply] instead of
    [apply].  Tactic [info_eauto] shows us which tactics [eauto] uses
    in its proof search.

    Below is an example of [eauto].  Before using it, we need to give
    some hints to [auto] about using the constructors of [ceval]
    and the definitions of [state] and [total_map] as part of its
    proof search. *)

Hint Constructors ceval : core.
Hint Transparent state total_map : core.

Example eauto_example : exists s',
  (Y !-> 1 ; X !-> 2) =[
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  ]=> s'.
Proof. info_eauto. Qed.

(** The [eauto] tactic works just like [auto], except that it uses
    [eapply] instead of [apply]; [info_eauto] shows us which facts
    [eauto] uses. *)


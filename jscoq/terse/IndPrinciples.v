(** * IndPrinciples: Induction Principles *)

(** Let's take a deeper look at induction. *)

Set Warnings "-notation-overridden".
From LF Require Export ProofObjects.

(* ################################################################# *)
(** * Basics *)

(** The automatically generated _induction principle_ for [nat]: *)

Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.

(** In English: Suppose [P] is a property of natural numbers (that is,
      [P n] is a [Prop] for every [n]). To show that [P n] holds of all
      [n], it suffices to show:

      - [P] holds of [0]
      - for any [n], if [P] holds of [n], then [P] holds of [S n]. *)

(** We can directly use the induction principle with [apply]: *)

Theorem mul_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.  Qed.

(** Why the [induction] tactic is nicer than [apply]:
     - [apply] requires extra manual bookkeeping (the [intros] in the
       inductive case)
     - [apply] requires [n] to be left universally quantified
     - [apply] requires us to manually specify the name of the induction
       principle. *)

(** Rocq generates induction principles for every datatype defined with
    [Inductive], including those that aren't recursive. *)

(** If we define type [t] with constructors [c1] ... [cn],
    Rocq generates:

    t_ind : forall P : t -> Prop,
              ... case for c1 ... ->
              ... case for c2 ... -> ...
              ... case for cn ... ->
              forall n : t, P n

    The specific shape of each case depends on the arguments to the
    corresponding constructor. *)

(** An example with no constructor arguments: *)

Inductive time : Type :=
  | day
  | night.

Check time_ind :
  forall P : time -> Prop,
    P day ->
    P night ->
    forall t : time, P t.

(** An example with constructor arguments: *)

Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).

Check natlist_ind :
  forall P : natlist -> Prop,
    P nnil  ->
    (forall (n : nat) (l : natlist),
        P l -> P (ncons n l)) ->
    forall l : natlist, P l.

(** In general, the automatically generated induction principle for
    inductive type [t] is formed as follows:

    - Each constructor [c] generates one case of the principle.
    - If [c] takes no arguments, that case is:

      "P holds of c"

    - If [c] takes arguments [x1:a1] ... [xn:an], that case is:

      "For all x1:a1 ... xn:an,
          if [P] holds of each of the arguments of type [t],
          then [P] holds of [c x1 ... xn]"

      But that oversimplifies a little.  An assumption about [P]
      holding of an argument [x] of type [t] actually occurs
      immediately after the quantification of [x].
*)

(** For example, suppose we had written the definition of [natlist] a little
    differently: *)

Inductive natlist' : Type :=
  | nnil'
  | nsnoc (l : natlist') (n : nat).

(** Now the induction principle case for [nsnoc] is a bit different
    than the earlier case for [ncons]: *)

Check natlist'_ind :
  forall P : natlist' -> Prop,
    P nnil' ->
    (forall l : natlist', P l -> forall n : nat, P (nsnoc l n)) ->
    forall n : natlist', P n.



(* ################################################################# *)
(** * Induction Principles for Propositions *)

(** Inductive definitions of propositions also cause Rocq to generate
    induction priniciples.  For example, recall our proposition [ev]
    from [IndProp]: *)

Print ev.

(* ===>

  Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)))

*)

Check ev_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, ev n -> P n -> P (S (S n))) ->
    forall n : nat, ev n -> P n.

(** In English, [ev_ind] says: Suppose [P] is a property of natural
    numbers.  To show that [P n] holds whenever [n] is even, it suffices
    to show:

      - [P] holds for [0],

      - for any [n], if [n] is even and [P] holds for [n], then [P]
        holds for [S (S n)]. *)

(** The precise form of an [Inductive] definition can affect the
    induction principle Rocq generates. *)

Inductive le1 : nat -> nat -> Prop :=
  | le1_n : forall n, le1 n n
  | le1_S : forall n m, (le1 n m) -> (le1 n (S m)).

Notation "m <=1 n" := (le1 m n) (at level 70).

(** [n] could instead be a parameter:  *)

Inductive le2 (n:nat) : nat -> Prop :=
  | le2_n : le2 n n
  | le2_S m (H : le2 n m) : le2 n (S m).

Notation "m <=2 n" := (le2 m n) (at level 70).

Check le1_ind :
  forall P : nat -> nat -> Prop,
    (forall n : nat, P n n) ->
    (forall n m : nat, n <=1 m -> P n m -> P n (S m)) ->
    forall n n0 : nat, n <=1 n0 -> P n n0.

Check le2_ind :
  forall (n : nat) (P : nat -> Prop),
    P n ->
    (forall m : nat, n <=2 m -> P m -> P (S m)) ->
    forall n0 : nat, n <=2 n0 -> P n0.

(** The latter is simpler, and corresponds to Rocq's own
    definition. *)

(* ################################################################# *)
(** * Explicit Proof Objects for Induction *)

(** Recall again the induction principle on naturals that Rocq generates for
    us automatically from the Inductive declaration for [nat]. *)

Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.

(** There's nothing magic about this induction lemma: it's just
   another Rocq lemma that requires a proof.  Rocq generates the proof
   automatically too...  *)

Print nat_ind.

(** We can rewrite that more tidily as follows: *)
Fixpoint build_proof
         (P : nat -> Prop)
         (evPO : P 0)
         (evPS : forall n : nat, P n -> P (S n))
         (n : nat) : P n :=
  match n with
  | 0 => evPO
  | S k => evPS k (build_proof P evPO evPS k)
  end.

Definition nat_ind_tidy := build_proof.

(** Recursive function [build_proof] thus pattern matches against
    [n], recursing all the way down to 0, and building up a proof
    as it returns. *)

(** We can use our own hand-coded induction principle in place
    of the automatically-generated induction principle with the
    [induction ... using ...] variant of the usual [induction]
    tactic. *)

Theorem mul_0_r''' : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [ | n' IHn'] using nat_ind_tidy.
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.


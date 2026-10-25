(** * Logic: Logic in Rocq *)

Set Warnings "-notation-overridden".
Require Nat.
From LF Require Export Tactics.

(** So far, we have seen...

       - _propositions_: mathematical statements, so far only of 3 kinds:
             - equality propositions ([e1 = e2])
             - implications ([P -> Q])
             - quantified propositions ([forall x, P])

       - _proofs_: ways of presenting evidence for the truth of a
          proposition

    In this chapter we will introduce several more flavors of both
    propositions and proofs. *)

(* ################################################################# *)
(** * The [Prop] Type *)

(** Like everything in Rocq, well-formed propositions have a _type_: *)

Check (forall n m : nat, n + m = m + n) : Prop.

(** Note that _all_ syntactically well-formed propositions have type
    [Prop] in Rocq, regardless of whether they are true or not.

    Simply _being_ a proposition is one thing; being _provable_ is
    a different thing! *)

Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.

(** So far, we've seen one primary place where propositions can appear:
    in [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** Propositions are first-class entities in Rocq, though. For
    example, we can name them: *)

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity.  Qed.

(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

(** In Rocq, functions that return propositions are said to define
    _properties_ of their arguments.

    For instance, here's a (polymorphic) property defining the
    familiar notion of an _injective function_. *)

Definition injective {A B} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros x y H. injection H as H1. apply H1.
Qed.

(** The familiar equality operator [=] is a (binary) function that returns
    a [Prop].

    The expression [n = m] is syntactic sugar for [eq n m] (defined in
    Rocq's standard library using the [Notation] mechanism).

    Because [eq] can be used with elements of any type, it is also
    polymorphic: *)

Check @eq : forall A : Type, A -> A -> Prop.

(* QUIZ

    What is the type of the following expression?

       pred (S O) = O

   (A) [Prop]

   (B) [nat->Prop]

   (C) [forall n:nat, Prop]

   (D) [nat->nat]

   (E) Not typeable







*)
Check (pred (S O) = O) : Prop.

(* QUIZ

    What is the type of the following expression?

      forall n:nat, pred (S n) = n

   (A) [Prop]

   (B) [nat->Prop]

   (C) [forall n:nat, Prop]

   (D) [nat->nat]

   (E) Not typeable







*)
Check (forall n:nat, pred (S n) = n) : Prop.

(* QUIZ

    What is the type of the following expression?

      forall n:nat, S (pred n) = n

   (A) [Prop]

   (B) [nat->Prop]

   (C) [nat->nat]

   (D) Not typeable







*)
Check (forall n:nat, S (pred n) = n) : Prop.

(* QUIZ

    What is the type of the following expression?

      forall n:nat, S (pred n)

   (A) [Prop]

   (B) [nat->Prop]

   (C) [nat->nat]

   (D) Not typeable







*)
Fail Check (forall n:nat, S (pred n)).
(* The command has indeed failed with message:
   In environment
   n : nat
   The term "(S (pred n))" has type "nat" which should be Set, Prop or Type. *)

(* QUIZ

    What is the type of the following expression?

      fun n:nat => S (pred n)

   (A) [Prop]

   (B) [nat->Prop]

   (C) [nat->nat]

   (D) Not typeable






*)
Check (fun n:nat => pred (S n)) : nat -> nat.

(* QUIZ

    What is the type of the following expression?

      fun n:nat => S (pred n) = n

   (A) [Prop]

   (B) [nat->Prop]

   (C) [nat->nat]

   (D) Not typeable







*)
Check (fun n:nat => pred (S n) = n) : nat -> Prop.

(* QUIZ

    Which of the following is _not_ a proposition?

    (A) [3 + 2 = 4]

    (B) [3 + 2 = 5]

    (C) [3 + 2 =? 5]

    (D) [((3+2) =? 4) = false]

    (E) [forall n, (((3+2) =? n) = true) -> n = 5]

    (F) All of these are propositions






*)
Check 3 + 2 =? 5 : bool.
Fail Definition bad : Prop := 3 + 2 =? 5.
(* The command has indeed failed with message: *)
(* The term "3 + 2 =? 5" has type "bool" while it is expected to have
   type "Prop". *)

(* ################################################################# *)
(** * Logical Connectives *)

(* ================================================================= *)
(** ** Conjunction *)

(** The _conjunction_, or _logical and_, of propositions [A] and [B] is
    written [A /\ B]; it represents the claim that both [A] and [B] are
    true. *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** To prove a conjunction, start with the [split] tactic.  This will
    generate two subgoals, one for each part of the statement: *)

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

(** For any propositions [A] and [B], if we assume that [A] and [B]
    are each true individually, we can conclude that [A /\ B] is also
    true.  The Rocq library provides a function [conj] that does this. *)

Check @conj : forall A B : Prop, A -> B -> A /\ B.

(** we can [apply conj] to achieve the same effect as [split]. *)

Example plus_is_O :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
    (* WORK IN CLASS *) Admitted.

(** So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to help prove
    something else -- we can use our good old [destruct] tactic. *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORK IN CLASS *) Admitted.

(** As usual, we can also destruct [H] right at the point where we
    introduce it, instead of introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** The infix notation [/\] is actually just syntactic sugar for
    [and A B].  That is, [and] is a Rocq operator that takes two
    propositions as arguments and yields a proposition. *)

Check and : Prop -> Prop -> Prop.

(* ================================================================= *)
(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_,
    of two propositions: [A \/ B] is true when either [A] or [B] is.
    This infix notation stands for [or A B], where
    [or : Prop -> Prop -> Prop]. *)

(** To use a disjunctive hypothesis in a proof, we proceed by case
    analysis -- which, as with other data types like [nat], can be done
    explicitly with [destruct] or implicitly with an [intros]
    pattern: *)

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This intro pattern implicitly does case analysis on
     [n = 0 \/ m = 0]... *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** Conversely, to show that a disjunction holds, it suffices to show
    that one of its sides holds. This can be done via the tactics
    [left] and [right].  As their names imply, the first one requires
    proving the left side of the disjunction, while the second
    requires proving the right side.  Here is a trivial use... *)

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** ... and here is a slightly more interesting example requiring both
    [left] and [right]: *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORK IN CLASS *) Admitted.

(** **** Exercise: 2 stars, standard (mult_is_O) *)
Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (or_commut) *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Falsehood and Negation *)

(** Up to this point, we have mostly been concerned with proving
    "positive" statements -- addition is commutative, appending lists
    is associative, etc.  We are sometimes also interested in negative
    results, demonstrating that some proposition is _not_ true. Such
    statements are expressed with the logical negation operator [~]. *)

(** To see how negation works, recall the _principle of explosion_
    from the [Tactics] chapter, which asserts that, if we assume a
    contradiction, then any other proposition can be derived.

    Following this intuition, we could define [~ P] ("not [P]") as
    [forall Q, P -> Q]. *)

(** Rocq actually makes an equivalent but slightly different choice,
    defining [~ P] as [P -> False], where [False] is a specific
    un-provable proposition defined in the standard library. *)

Module NotPlayground.

Definition not (P:Prop) := P -> False.

Check not : Prop -> Prop.

Notation "~ x" := (not x) : type_scope.

End NotPlayground.

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we can get [False] into the context,
    we can use [destruct] on it to complete any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.  Qed.

(** Inequality is a very common form of negated statement, so there is a
    special notation for it: *)

Notation "x <> y" := (~(x = y)) : type_scope.

(** For example: *)

Theorem zero_not_one : 0 <> 1.
Proof.
    unfold not.
    intros contra.
    discriminate contra.
Qed.

(** It takes a little practice to get used to working with negation in Rocq.
    Even though _you_ may see perfectly well why a claim involving
    negation holds, it can be a little tricky at first to see how to make
    Rocq understand it!

    Here are proofs of a few familiar facts to help get you warmed up. *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORK IN CLASS *) Admitted.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORK IN CLASS *) Admitted.

(** Since inequality involves a negation, getting comfortable
    with it also often requires a little practice.

    A useful trick: if you are trying to prove a nonsensical goal,
    apply [ex_falso_quodlibet] to change the goal to [False]. This
    makes it easier to use assumptions of the form [~P], and in
    particular of the form [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H. destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we need
    besides [intros] and [apply]?

        forall X, forall a b : X, (a=b) /\ (a<>b) -> False.

    (A) [destruct], [unfold], [left] and [right]

    (B) [destruct] and [unfold]

    (C) only [destruct]

    (D) [left] and/or [right]

    (E) only [unfold]

    (F) none of the above

*)
Lemma quiz1: forall X, forall a b : X, (a=b) /\ (a<>b) -> False.
Proof.
  intros X a b [Hab Hnab]. apply Hnab. apply Hab.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we
    need besides [intros] and [apply]?

        forall P Q : Prop,  P \/ Q -> ~~(P \/ Q).

    (A) [destruct], [unfold], [left] and [right]

    (B) [destruct] and [unfold]

    (C) only [destruct]

    (D) [left] and/or [right]

    (E) only [unfold]

    (F) none of the above

*)
Lemma quiz2 : forall P Q : Prop,  P \/ Q -> ~~(P \/ Q).
Proof.
  intros P Q HPQ HnPQ. apply HnPQ in HPQ. apply HPQ.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we
    need besides [intros] and [apply]?

         forall P Q: Prop, P -> (P \/ ~~Q).

    (A) [destruct], [unfold], [left] and [right]

    (B) [destruct] and [unfold]

    (C) only [destruct]

    (D) [left] and/or [right]

    (E) only [unfold]

    (F) none of the above

*)
Lemma quiz3 : forall P Q: Prop, P -> (P \/ ~~Q).
Proof.
intros P Q HP. left. apply HP.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we need
    besides [intros] and [apply]?

         forall P Q: Prop,  P \/ Q -> ~~P \/ ~~Q.

    (A) [destruct], [unfold], [left] and [right]

    (B) [destruct] and [unfold]

    (C) only [destruct]

    (D) [left] and/or [right]

    (E) only [unfold]

    (F) none of the above

*)
Lemma quiz4 : forall P Q: Prop,  P \/ Q -> ~~P \/ ~~Q.
Proof.
  intros P Q [HP | HQ].
  - (* left *)
    left. intros HnP. apply HnP in HP. apply HP.
  - (* right *)
    right. intros HnQ. apply HnQ in HQ. apply HQ.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we need
    besides [intros] and [apply]?

         forall A : Prop, 1=0 -> (A \/ ~A).

    (A) [discriminate], [unfold], [left] and [right]

    (B) [discriminate] and [unfold]

    (C) only [discriminate]

    (D) [left] and/or [right]

    (E) only [unfold]

    (F) none of the above

*)
Lemma quiz5 : forall A : Prop, 1=0 -> (A \/ ~A).
Proof.
  intros P H. discriminate H.
Qed.

(* ================================================================= *)
(** ** Truth *)

(** Besides [False], Rocq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    constant [I : True], which is also defined in the standard
    library: *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** Unlike [False], which is used extensively, [True] is used
    relatively rarely: it is trivial (and therefore uninteresting) to
    prove as a goal, and it provides no useful information when it
    appears as a hypothesis. *)

(* ================================================================= *)
(** ** Logical Equivalence *)
Print "<->".
(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is simply the conjunction
    of two implications.

      Print "<->".
*)
(* ===>
     Notation "A <-> B" := (iff A B)

     iff = fun A B : Prop => (A -> B) /\ (B -> A)
         : Prop -> Prop -> Prop

     Argumments iff (A B)%type_scope  *)

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORK IN CLASS *) Admitted.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

(** The [apply] tactic can also be used with [<->]. *)

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R Hiff H HP. apply H. apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R Hiff H HQ. apply H. apply Hiff. apply HQ.
Qed.

(** **** Exercise: 1 star, standard, optional (iff_properties)

    Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Setoids and Logical Equivalence *)

(** Some of Rocq's tactics treat [iff] statements specially, avoiding some
    low-level proof-state manipulation.  In particular, [rewrite] and
    [reflexivity] can be used with [iff] statements, not just equalities.
    To enable this behavior, we have to import the Rocq library that
    supports it: *)
From Stdlib Require Import Setoids.Setoid.

(** A "setoid" is a set equipped with an equivalence relation,
    such as [=] or [<->]. *)

(** Here is a simple example demonstrating how these tactics work with
    [iff].

    First, let's prove a couple of basic iff equivalences. (For these
    proofs we are not using setoids yet.) *)

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** We can now use these facts with [rewrite] and [reflexivity] to
    prove a ternary version of the [mult_eq_0] fact above _without_
    splitting the top-level iff: *)

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Existential Quantification *)

(** To prove a statement of the form [exists x, P], we must show that [P]
    holds for some specific choice for [x], known as the _witness_ of the
    existential.  This is done in two steps: First, we explicitly tell Rocq
    which witness [t] we have in mind by invoking the tactic [exists t].
    Then we prove that [P] holds after all occurrences of [x] are replaced
    by [t]. *)

Definition Even x := exists n : nat, x = double n.
Check Even : nat -> Prop.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORK IN CLASS *) Admitted.

(* ================================================================= *)
(** ** Recap -- Logical connectives in Rocq *)

(** Basic connectives:
       - [and : Prop -> Prop -> Prop] (conjunction):
         - introduced with the [split] tactic
         - eliminated with [destruct H as [H1 H2]]
       - [or : Prop -> Prop -> Prop] (disjunction):
         - introduced with [left] and [right] tactics
         - eliminated with [destruct H as [H1 | H2]]
       - [False : Prop]
         - eliminated with [destruct H as []]
       - [True : Prop]
         - introduced with [apply I], but not as useful
       - [ex : forall A:Type, (A -> Prop) -> Prop] (existential)
         - introduced with [exists w]
         - eliminated with [destruct H as [x H]]

    Derived connectives:
       - [not : Prop -> Prop] (negation):
         - [not P] defined as [P -> False]
       - [iff : Prop -> Prop -> Prop] (logical equivalence):
         - [iff P Q] defined as [(P -> Q) /\ (Q -> P)]

    Fundamental connectives we've been using since the beginning:
       - equality ([e1 = e2])
       - implication ([P -> Q])
       - universal quantification ([forall x, P]) *)

(* ################################################################# *)
(** * Programming with Propositions *)

(** What does it mean to say that "an element [x] occurs in a
    list [l]"?

       - If [l] is the empty list, then [x] cannot occur in it, so the
         property "[x] appears in [l]" is simply false.

       - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
         occurs in [l] if it is equal to [x'] or it occurs in [l']. *)

(** We can translate this directly into a straightforward recursive
    function taking an element and a list and returning... a proposition! *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORK IN CLASS *) Admitted.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORK IN CLASS *) Admitted.

(** We can also reason about more generic statements involving [In]. *)

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(* ################################################################# *)
(** * Applying Theorems to Arguments *)

(** Rocq also treats _proofs_ as first-class objects! *)

(** We have seen that we can use [Check] to ask Rocq to check whether
    an expression has a given type: *)

Check plus : nat -> nat -> nat.
Check @rev : forall X, list X -> list X.

(** We can also use it to check what theorem a particular identifier
    refers to: *)

Check add_comm        : forall n m : nat, n + m = m + n.
Check plus_id_example : forall n m : nat, n = m -> n + n = m + m.

(** Rocq checks the _statements_ of the [add_comm] and
    [plus_id_example] theorems in the same way that it checks the
    _type_ of any term (e.g., plus). If we leave off the colon and
    type, Rocq will print these types for us.

    Why? *)

(** The reason is that the identifier [add_comm] actually refers to a
    _proof object_ -- a logical derivation establishing the truth of the
    statement [forall n m : nat, n + m = m + n].  The type of this object
    is the proposition that it is a proof of.

    The type of an ordinary function tells us what we can do with it.
       - If we have a term of type [nat -> nat -> nat], we can give it two
         [nat]s as arguments and get a [nat] back.

    Similarly, the statement of a theorem tells us what we can use that
    theorem for.
       - If we have a term of type [forall n m, n = m -> n + n = m + m] and we
         provide it two numbers [n] and [m] and a third "argument" of type
         [n = m], we get back a proof object of type [n + n = m + m]. *)

(** Rocq actually allows us to _apply_ a theorem as if it were a
    function.

    This is often handy in proof scripts -- e.g., suppose we want too
    prove the following: *)

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.

(** It appears at first sight that we ought to be able to prove this by
    rewriting with [add_comm] twice to make the two sides match.  The
    problem is that the second [rewrite] will undo the effect of the
    first. *)

Proof.
  intros x y z.
  rewrite add_comm.
  rewrite add_comm.
  (* We are back where we started... *)
Abort.

(** We can fix this by applying [add_comm] to the arguments we want
    it be to instantiated with.  Then the [rewrite] is forced to happen
    exactly where we want it. *)

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

(** Here's another example of using a theorem about lists like
    a function.  Suppose we have proved the following simple fact
    about lists... *)

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

(** Note that one quantified variable ([x]) does not appear in
    the conclusion ([l <> []]). *)

(** Intuitively, we should be able to use this theorem to prove the special
    case where [x] is [42]. However, simply invoking the tactic [apply
    in_not_nil] will fail because it cannot infer the value of [x]. *)

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

(** There are several ways to work around this: *)

(** We can use [apply ... with ...]: *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(** Or we can use [apply ... in ...]: *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(** Or -- this is the new one -- we can explicitly
    apply the lemma to the value [42] for [x]: *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(** We can also explicitly apply the lemma to a hypothesis,
    causing the values of the other parameters to be inferred: *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Lemma quiz : forall a b : nat,
  a = b -> b = 42 ->
  (forall (X : Type) (n m o : X),
          n = m -> m = o -> n = o) ->
  True.
Proof.
  intros a b H1 H2 trans_eq.

(* QUIZ

    Suppose we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o

    What is the type of this "proof object"?

      trans_eq nat a b 42 H1 H2

    (A) [a = b]

    (B) [42 = a]

    (C) [a = 42]

    (D) Does not typecheck







 *)
Check trans_eq nat a b 42 H1 H2
  : a = 42.



(* QUIZ

    Suppose, again, that we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o

    What is the type of this proof object?

      trans_eq nat _ _ _ H1 H2

    (A) [a = b]

    (B) [42 = a]

    (C) [a = 42]

    (D) Does not typecheck





 *)
Check trans_eq nat _ _ _ H1 H2
  : a = 42.



(* QUIZ

    Suppose, again, that we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o

    What is the type of this proof object?

      trans_eq nat b 42 a H2

    (A) [b = a]

    (B) [b = a -> 42 = a]

    (C) [42 = a -> b = a]

    (D) Does not typecheck





 *)
Check trans_eq nat b 42 a H2
    : 42 = a -> b = a.



(* QUIZ

    Suppose, again, that we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o

    What is the type of this proof object?

      trans_eq _ 42 a b

    (A) [a = b -> b = 42 -> a = 42]

    (B) [42 = a -> a = b -> 42 = b]

    (C) [a = 42 -> 42 = b -> a = b]

    (D) Does not typecheck





 *)
Check trans_eq _ 42 a b
    : 42 = a -> a = b -> 42 = b.



(* QUIZ

    Suppose, again, that we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
                   n = m -> m = o -> n = o

    What is the type of this proof object?

      trans_eq _ _ _ _ H2 H1

    (A) [b = a]

    (B) [42 = a]

    (C) [a = 42]

    (D) Does not typecheck





 *)
Fail Check trans_eq _ _ _ _ H2 H1.

Abort.

(* ################################################################# *)
(** * Working with Decidable Properties *)

(** We've seen two different ways of expressing logical claims in Rocq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

    Here are the key differences between [bool] and [Prop]:

                                           bool     Prop
                                           ====     ====
           decidable?                      yes       no
           useable with match?             yes       no
           works with rewrite tactic?      no        yes
*)

(** Since every function terminates on all inputs in Rocq, a function
    of type [nat -> bool] is a _decision procedure_ -- i.e., it yields
    [true] or [false] on all inputs.

      - For example, [even : nat -> bool] is a decision procedure for the
        property "is even". *)

(** It follows that there are some properties of numbers that we _cannot_
    express as functions of type [nat -> bool].

      - For example, the property "is the code of a halting Turing machine"
        is undecidable, so there is no way to write it as a function of
        type [nat -> bool].

    On the other hand, [nat->Prop] is the type of _all_ properties of
    numbers that can be expressed in Rocq's logic, including both decidable
    and undecidable ones.

      - For example, "is the code of a halting Turing machine" is a
        perfectly legitimate mathematical property, and we can absolutely
        represent it as a Rocq expression of type [nat -> Prop].
*)

(** Since [Prop] includes _both_ decidable and undecidable properties, we
    have two options when we want to formalize a property that happens to
    be decidable: we can express it either as a boolean computation or as a
    function into [Prop]. *)

(** For instance, to claim that a number [n] is even, we can say
    either that [even n] evaluates to [true]... *)
Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

(** ... or that there exists some [k] such that [n = double k]. *)
Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

(** Of course, it would be deeply strange if these two
    characterizations of evenness did not describe the same set of
    natural numbers!

    Fortunately, they do! *)

(** To prove this, we first need two helper lemmas. *)

Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  (* Hint: Use the [even_S] lemma from [Induction.v]. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Now the main theorem: *)

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

(** In view of this theorem, we can say that the boolean computation
    [even n] is _reflected_ in the truth of the proposition
    [exists k, n = double k]. *)

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either
      - (1) that [n =? m] returns [true], or
      - (2) that [n = m].
    Again, these two notions are equivalent: *)

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

(** So what should we do in situations where some claim could be
    formalized as either a proposition or a boolean computation? Which
    should we choose?

    In general, _both_ can be useful. *)

(** For example, booleans are more useful for defining functions.
    There is no effective way to _test_ whether or not a [Prop] is
    true, so we cannot use [Prop]s in conditional expressions. The
    following definition is rejected: *)

Fail
Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Rather, we have to state this definition using a boolean equality
    test. *)

Definition is_even_prime n :=
  if n =? 2 then true
  else false.

(** More generally, stating facts using booleans can often enable
    effective proof automation through computation with Rocq terms, a
    technique known as _proof by reflection_.

    Consider the following statement: *)

Example even_1000 : Even 1000.

(** The most direct way to prove this is to give the value of [k]
    explicitly. *)

Proof. unfold Even. exists 500. reflexivity. Qed.

(** The proof of the corresponding boolean statement is simpler, because we
    don't have to invent the witness [500]: Rocq's computation mechanism
    does it for us! *)

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

(** Now, the useful observation is that, since the two notions are
    equivalent, we can use the boolean formulation to prove the other one
    without mentioning the value 500 explicitly: *)

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Although we haven't gained much in terms of proof-script
    line count in this case, larger proofs can often be made considerably
    simpler by the use of reflection.  As an extreme example, a famous
    Rocq proof of the even more famous _4-color theorem_ uses
    reflection to reduce the analysis of hundreds of different cases
    to a boolean computation. *)

(** Another advantage of booleans is that the _negation_ of a claim
    about booleans is straightforward to state and (when true) prove:
    simply flip the expected boolean result. *)

Example not_even_1001 : even 1001 = false.
Proof.
  reflexivity.
Qed.

(** In contrast, propositional negation can be difficult to work with
    directly.

    For example, suppose we state the non-evenness of [1001]
    propositionally: *)

Example not_even_1001' : ~(Even 1001).

(** Proving this directly -- by assuming that there is some [n] such that
    [1001 = double n] and then somehow reasoning to a contradiction --
    would be rather complicated.

    But if we convert it to a claim about the boolean [even] function, we
    can let Rocq do the work for us. *)

Proof.
  (* WORK IN CLASS *) Admitted.

(** Conversely, there are situations where it can be easier to work
    with propositions rather than booleans.

    In particular, knowing that [(n =? m) = true] is generally of
    little direct help in the middle of a proof involving [n] and [m].
    But if we convert the statement to the equivalent form [n = m],
    then we can easily [rewrite] with it. *)

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORK IN CLASS *) Admitted.

(** Being able to cross back and forth between the boolean and
    propositional worlds will often be convenient in later chapters. *)

(* ################################################################# *)
(** * The Logic of Rocq *)

(** Rocq's logical core, the _Calculus of Inductive Constructions_,
    is a "metalanguage for mathematics" in the same sense as familiar
    foundations for paper-and-pencil math, like Zermelo-Fraenkel Set
    Theory (ZFC).

    Mostly, the differences are not too important, but a few points are
    useful to understand. *)

(* ================================================================= *)
(** ** Functional Extensionality *)

(** Rocq's logic is quite minimalistic.  This means that one occasionally
    encounters cases where translating standard mathematical reasoning into
    Rocq is cumbersome -- or even impossible -- unless we enrich its core
    logic with additional axioms. *)

(** A first instance has to do with equality of functions.

    In certain cases Rocq can successfully prove equality propositions stating
    that two _functions_ are equal to each other: **)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

(** This works when Rocq can simplify the functions to the same expression,
    but this doesn't always happen. **)

(** These two functions are equal just by simplification, but in general
    functions can be equal for more interesting reasons.

    In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same output on every input:

    (forall x, f x = g x) -> f = g

    This is known as the principle of _functional extensionality_. *)

(** However, functional extensionality is not part of Rocq's built-in logic.
    This means that some intuitively obvious propositions are not
    provable. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  Fail reflexivity. Fail rewrite add_comm.
  (* Stuck *)
Abort.

(** However, if we like, we can add functional extensionality to Rocq
    using the [Axiom] command. *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** Defining something as an [Axiom] has the same effect as stating a
    theorem and skipping its proof using [Admitted], but it alerts the
    reader that this isn't just something we're going to come back and
    fill in later! *)

(** We can now invoke functional extensionality in proofs: *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

(** Naturally, we need to be quite careful when adding new axioms into
    Rocq's logic, as this can render it _inconsistent_ -- that is, it may
    become possible to prove every proposition, including [False], [2+2=5],
    etc.!

    In general, there is no simple way of telling whether an axiom is safe
    to add: hard work by highly trained mathematicians is often required to
    establish the consistency of any particular combination of axioms.

    Fortunately, it is known that adding functional extensionality, in
    particular, _is_ consistent. *)

(** To check whether a particular proof relies on any additional
    axioms, use the [Print Assumptions] command:

      Print Assumptions function_equality_ex2.
*)
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(* ================================================================= *)
(** ** Classical vs. Constructive Logic *)

(** The following reasoning principle is _not_ derivable in
    Rocq (though, again, it can consistently be added as an axiom): *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** Logics like Rocq's, which do not assume the excluded middle, are
    referred to as _constructive logics_.

    Logical systems such as ZFC, in which the excluded middle does
    hold for arbitrary propositions, are referred to as _classical_. *)


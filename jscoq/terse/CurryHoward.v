(** * CurryHoward: A Formal Development of the Curry-Howard Correspondence *)

(** In [ProofObjects] we saw that Rocq tactics construct _proof
    objects_: programs in Gallina whose types are the statements being proved.
    Thus, proving a theorem is also writing a program.

    This suggests a deeper connection: proofs transform evidence for
    assumptions into evidence for conclusions, just as functions transform
    inputs into outputs. Hence programs correspond to proofs, and types to
    propositions—this is the Curry–Howard correspondence.

    In this chapter we formalize that correspondence. We define a proof system
    for logic and a type system for programs, both inside Rocq. We show:
    - If a program is well-typed, its type corresponds to a provable proposition.
    - If a proposition is provable, there exists a well-typed program of that type.

    Thus, programs and proofs correspond in both directions.

    Why is this exciting? It reveals that logic and programming share the same
    underlying structure: logical connectives correspond to programming
    constructs, and proofs correspond to executable programs. *)

From Stdlib Require Import List String.
Import ListNotations.

(** We will first develop the correspondence in a setting that focuses
    on implication. Later we will add conjunction and disjunction. *)

Module Implicational.

(* ################################################################# *)
(** * Logic *)

(** So far we have been doing logic _with_ Rocq. To make the
    correspondence precise, we instead need to do logic _embedded in_ Rocq: we
    define propositions as an inductive type and provability as an inductive
    relation. The logic formalized here is known as _propositional constructive
    logic_.*)

(* ================================================================= *)
(** ** Propositions *)

(** We start by modeling propositions.

    - An _atom_ is an atomic proposition, much like [P] in [P : Prop], as we
      are accustomed to in Rocq. Atomic propositions are given names using
      Rocq [string]s.

    - An implication is the usual [P -> Q].

    - The contradictory proposition is named [false]. *)

Inductive proposition :=
  | atom (id : string)
  | implies (p q : proposition)
  | false.

(** From that starting point, we can define negation and truth in terms
    of other propositions. *)

Definition not (p : proposition) : proposition :=
  implies p false.

Definition true : proposition :=
  implies false false.

(** Here are some examples of propositions. *)

Definition ex_P :=
  (* P -> P *)
  implies (atom "P") (atom "P").

Definition ex_PQ :=
  (* P -> Q -> P *)
  implies (atom "P") (implies (atom "Q") (atom "P")).

Definition ex_PQR :=
  (* (P -> Q -> R) -> (P -> Q) -> P -> R *)
  implies
    (implies (atom "P") (implies (atom "Q") (atom "R")))
    (implies (implies (atom "P") (atom "Q")) (implies (atom "P") (atom "R"))).

(* ================================================================= *)
(** ** Proofs *)

(** A _proof system_ specifies how to construct correct proofs via
    axioms and inference rules. We use _natural deduction_, defined by a
    _provability_ relation.

    The relation [A |- p] means that proposition [p] is provable from
    assumptions [A]. We write [A, p] for [A] extended with [p]. *)

(**

        -------------------- (axiom)
              A, p |- p

              A, p |- q
        -------------------- (implies intro)
             A |- p -> q

        A |- p -> q   A |- p
        -------------------- (implies elim)
              A |- q

             A |- false
        -------------------- (false elim)
               A |- p

*)

(** The rules:

    - Axiom: proof "by assumption".
    - Implies intro: to prove an implication, assume its premise and
      prove its conclusion.
    - Implies elim (modus ponens): given an implication and a proof of
      its premise, you obtain a proof of its conclusion.
    - False elim: from a contradiction, anything follows.

    Introduction rules put a connective in the conclusion; elimination rules
    remove a connective from the premise(s). Implication represents a
    transformation from proofs of [p] to proofs of [q]. There is no rule for
    introducing [false]. *)

(** The natural deduction inference rules are straightforward to formalize
    in Rocq. It is convenient to represent the set of assumptions as a list,
    since we already have lots of experience with that type. *)

Inductive provable : list proposition -> proposition -> Prop :=
  | axiom : forall A p,
      In p A ->
      provable A p
  | implies_intro : forall A p q,
      provable (p :: A) q ->
      provable A (implies p q)
  | implies_elim : forall A p q,
      provable A (implies p q) ->
      provable A p ->
      provable A q
  | false_elim : forall A p,
      provable A false ->
      provable A p.

(** Here are some examples of using the proof system. *)

Example ex_P_provable : provable [] ex_P.
(*
         -------------------- (axiom)
                p |- p
         -------------------- (implies intro)
              |- p -> p
*)
Proof.
  unfold ex_P. apply implies_intro.
  apply axiom. simpl. left. reflexivity.
Qed.

Example ex_PQ_provable : provable [] ex_PQ.
(*
      ------------------- (axiom)
           P, Q |- P
      ------------------- (implies intro)
          P |- Q -> P
      ------------------- (implies intro)
        |- P -> Q -> P
*)
Proof.
  (* WORK IN CLASS *) Admitted.

Example ex_mp : forall (P Q : string),
  provable [implies (atom P) (atom Q); (atom P)] (atom Q).
(*
    ------------------- (axiom)     -------------- (axiom)
    P -> Q, P |- P -> Q             P -> Q, P |- P
    ---------------------------------------------- (implies elim)
                   P -> Q, P |- Q
*)
Proof.
  (* WORK IN CLASS *) Admitted.

(* QUIZ
    To prove [~P] from assumptions [P -> Q] and [~Q],
    we need to show [P -> false].

    What is the key intermediate proposition to derive?

    (A) [P]

    (B) [Q]

    (C) [false]

    (D) [P -> Q]





    We need [Q].
  - Start with [P].
  - Use [P->Q] to get [Q]. <-- That is the intermediate proposition.
  - Use [Q->false] to get [false].
 *)

(* QUIZ
    In a proof of [P -> Q, ~Q |- ~P], which rules are required?

    (A) [axiom] and [implies_intro]

    (B) [axiom] and [false_elim]

    (C) [axiom], [implies_elim], and [implies_intro]

    (D) [axiom], [implies_intro], and [false_elim]





*)
Example modus_tollens : forall (p q : proposition),
  provable [implies p q; not q] (not p).
Proof.
  intros p q. unfold not.
  apply implies_intro.
  apply implies_elim with q.
    - apply axiom. simpl. right. right. left. reflexivity.
    - apply implies_elim with p.
      + apply axiom. simpl. right. left. reflexivity.
      + apply axiom. simpl. left. reflexivity.
Qed.

(** The use of the [axiom] rule followed by reasoning about [In] gets tedious.
    We can automate it with the following little custom tactic. The techniques
    used in the tactic will be explained in [Auto] (or alternatively
    [AltAuto]). *)

Ltac by_assumption :=
  constructor;
  repeat match goal with
  | |- In ?p (?h :: ?t) => simpl
  | |- (?x = ?y) \/ ?p => first [left; reflexivity | right]
  | |- False => idtac "by_assumption failed: not in assumptions"; fail
  end.

Example in_assumptions : provable [atom "P"] (atom "P").
Proof.
  by_assumption.
Qed.

Example not_in_assumptions : provable [atom "Q"] (atom "P").
Proof.
  by_assumption.
Abort.

Example ex_P_provable' : provable [] ex_P.
Proof.
  unfold ex_P. apply implies_intro.
  by_assumption.
Qed.

(* ################################################################# *)
(** * Programs *)

(** Much like we just embedded logic in Rocq, we now need to embed a
    programming language in Rocq. The language we formalize here is known as
    the _simply-typed pure lambda calculus_. It is the core of any functional
    programming language.  *)

(* ================================================================= *)
(** ** Syntax *)

(** We start by modeling the types of programs.

    - A _type variable_ stands for an unknown type, much like the [X]
      in [X : Type] that we have used when defining polymorphic lists
      in Rocq. We again use Rocq [string]s as identifiers.

    - An _arrow_ represents a function type, like [t1 -> t2] in Rocq. *)

Inductive type :=
  | tvar (id : string)
  | arrow (t1 t2 : type).

(** Next, we model program _expressions_ (aka _terms_).

    - As usual we have _variables_.

    - A function aka _abstraction_ is like [fun (x : t) => e] in Rocq.
      It binds a variable, explicitly states the type of that variable,
      and has an expression as its body.

    - An _application_ applies a function to an argument, like [e1 e2] in
      Rocq.*)

Inductive expr :=
  | var (id : string)
  | abs (id : string) (t : type) (e : expr)
  | app (e1 e2 : expr).

(** Here are some examples of programs. *)

Definition e_I : expr :=
  (* fun (x:T) => x *)
  abs "x" (tvar "T") (var "x").

Definition e_K : expr :=
  (* fun (x:T) (y:U) => x *)
  abs "x" (tvar "T") (abs "y" (tvar "U") (var "x")).

Definition e_S : expr :=
  (* fun (x:T->U->V) (y:T->U) (z:T) => x z (y z) *)
  abs "x" (arrow (tvar "T") (arrow (tvar "U") (tvar "V")))
    (abs "y" (arrow (tvar "T") (tvar "U"))
      (abs "z" (tvar "T")
        (app (app (var "x") (var "z"))
             (app (var "y") (var "z"))))).

(* ================================================================= *)
(** ** Type Checking *)

(** A _type system_ specifies when programs are well-typed.
    The typing relation [E |- e : t] means expression [e] has type [t]
    under environment [E], which maps variables to types. We write
    [E, x:t] to extend [E] with a binding for identifier [x] at type [t]. *)

(** The typing relation is defined with the following inference rules:

        ---------------------------------- (t-var)
                E, x : t |- x : t

              E, x : t1 |- e : t2
        ---------------------------------- (t-abs)
        E |- fun (x : t1) => e : t1 -> t2

        E |- e1 : t1 -> t2    E |- e2 : t1
        ---------------------------------- (t-app)
                 E |- e1 e2 : t2

*)

(** The rules:

    - T-Var: a variable has the type assigned to it in the environment.

    - T-Abs: to type a function, assume its parameter has a given type
      and type-check the body.

    - T-App: to type a function application, type-check the function
      and its argument, then use the function's output type. *)

(** As a simple representation of partial maps, we use an _association list_,
    that is, a list of pairs, where the first component of the pair is a _key_
    and the second component is the value to which that key is bound. For
    simplicity, we omit any checking to prohibit duplicate keys. *)

Definition tenv := list (string * type).

(** The type system inference rules are straightforward to formalize in Rocq. *)

Inductive hastype : tenv -> expr -> type -> Prop :=
  | t_var : forall E x t,
      In (x, t) E ->
      hastype E (var x) t
  | t_abs : forall E x t1 e t2,
      hastype ((x, t1) :: E) e t2 ->
      hastype E (abs x t1 e) (arrow t1 t2)
  | t_app : forall E e1 t1 t2 e2,
      hastype E e1 (arrow t1 t2) ->
      hastype E e2 t1 ->
      hastype E (app e1 e2) t2.

(** The example programs given above are all well-typed. Our [by_assumption]
    tactic continues to work equally well for association lists. *)

Example e_I_typable :
  hastype [] e_I (arrow (tvar "T") (tvar "T")).
(*
        ---------------------------- (t-var)
               x : T |- x : T
        ---------------------------- (t-abs)
        |- fun (x : T) => x : T -> T
*)
Proof.
  unfold e_I. apply t_abs. by_assumption.
Qed.

Example e_K_typable :
  hastype [] e_K (arrow (tvar "T") (arrow (tvar "U") (tvar "T"))).
(*
      ------------------------------------------------ (t-var)
                   x : T, y : U |- x : T
      ------------------------------------------------ (t-abs)
            x : T |- fun (y : U) => x : U -> T
      ------------------------------------------------ (t-abs)
      |- fun (x : T) => fun (y : U) => x : T -> U -> T
*)
Proof.
  (* WORK IN CLASS *) Admitted.

(* ################################################################# *)
(** * The Correspondence *)

(** Using the formalizations of provability and typability, we can now
    make the Curry-Howard correspondence precise. *)

(* ================================================================= *)
(** ** Arrow Elimination *)

(** First, consider the rules that involve eliminating an arrow, whether it's a
    function type arrow or an implication arrow: *)

(**

        E |- e1 : t1 -> t2    E |- e2 : t1
        ---------------------------------- (t-app)
                E |- e1 e2 : t2

            A |- p -> q         A |- p
        ---------------------------------- (implies elim)
                     A |- q

*)

(** Observe what happens if we erase from [t-app] everything between
    each turnstile [|-] (exclusive) and colon (inclusive): *)

(**

            E |- t1 -> t2       E |- t1
        ---------------------------------- (t-app-erased)
                     E |- t2

            A |- p -> q         A |- p
        ---------------------------------- (implies elim)
                     A |- q

*)

(** Erasing programs from [t-app] yields [implies elim]!

    Both rules express _transformation_:

    - Implication maps proofs of [p] to proofs of [q]
    - Functions map inputs of type [t1] to outputs of type [t2].

    The typing rule just adds the code that performs the transformation. *)

(* ================================================================= *)
(** ** Arrow Introduction *)

(** Second, consider the rules that involve introducing an arrow: *)

(**

              E, x : t1 |- e : t2
        --------------------------------- (t-abs)
        E |- fun (x : t1) => e : t1 -> t2

                    A, p |- q
        --------------------------------- (implies intro)
                   A |- p -> q

*)

(** As before, if we erase the programs from [t-abs], we obtain a rule
    that looks exactly like [implies introduction]: *)

(**

                   E, t1 |- t2
        --------------------------------- (t-abs-erased)
                  E |- t1 -> t2

                    A, p |- q
        --------------------------------- (implies intro)
                   A |- p -> q
*)

(** Both rules create a transformer: implication on proofs, functions on values.
    The typing rule includes the code that implements the transformation. *)

(* ================================================================= *)
(** ** Assumptions *)

(** Third and finally, consider the rules that involve assumptions, and the
    erasure of the typing rule: *)

(**

        ----------------- (t-var)
        E, x : t |- x : t

        ----------------- (t-var-erased)
            E, t |- t

        ----------------- (axiom)
            A, p |- p

*)

(** Again, [t-var-erased] looks exactly like its logical companion [axiom].
    The rules are expressing the same basic principle of reasoning "by
    assumption." *)

(* QUIZ
    What proposition does the following program prove?
    (Assume that T and U are types in scope.)

        fun (f : T -> U) => f

    (A) T -> U

    (B) (T -> U) -> (T -> U)

    (C) (T -> U) -> T

    (D) T -> (T -> U)




*)
Definition itproves1 := fun (T U : Type) =>
  fun (f : T -> U) => f.
Check itproves1 : forall T U : Type,
  (T -> U) -> T -> U.

(* QUIZ
    What proposition does the following program prove?

        fun (f : T -> U) =>
        fun (x : T) =>
          f x

    A. T -> U
    B. (T -> U) -> T -> U
    C. (T -> U) -> U
    D. T -> (T -> U)





*)
Definition itproves2 := fun (T U : Type) =>
  fun (f : T -> U) => fun (x : T) => f x.
Check itproves2 : forall T U : Type,
  (T -> U) -> T -> U.

(* ================================================================= *)
(** ** Proving the Correspondence *)

(** We saw above that by erasing programs from typability rules, we are
    left essentially with provability rules. Thus, any derivation of
    the type of a program also establishes a derivation of the provability
    of a corresponding proposition. *)

(** For example, here is a derivation of the type [X -> (Y -> X)] of a program:

        ------------------------------------------------- (t-var)
                         x:X, y:Y |- x : X
        ------------------------------------------------- (t-abs)
                  x:X |- fun (y:Y) => x : Y -> X
        ------------------------------------------------- (t-abs)
        |- fun (x:X) => (fun (y:Y) => x)) : X -> (Y -> X)

And by erasing the code from that derivation we are left with a derivation
of the provability of [X -> (Y -> X)]:

        ---------------- (axiom)
            X, Y |- X
        ---------------- (implies introduction)
          X |- Y -> X
        ---------------- (implies introduction)
        |- X -> (Y -> X)

*)

(** Therefore, our logical proof system rules are in a correspondence with our
    type system rules:

    - [axiom] corresponds to [t_var].

    - [implies_intro] corresponds to [t_abs].

    - [implies_elim] corresponds to [t_app].

    And therefore there is a correspondence between logical connectives and
    programming language features:

    - _Propositional variables_ correspond to _program variables_.

    - _Implication_ corresponds to _functions and application_.

    *)

(** There is a small mismatch, however, between our data structures for
    types and propositions. We can use the following function to
    convert a type to a proposition: *)

Fixpoint proposition_of_type (t : type) : proposition :=
  match t with
  | tvar x => atom x
  | arrow t1 t2 =>
    implies (proposition_of_type t1) (proposition_of_type t2)
  end.

Example pot_XY :
  proposition_of_type
    (arrow (tvar "X") (arrow (tvar "Y") (tvar "X")))
  =
    (implies (atom "X") (implies (atom "Y") (atom "X"))).
Proof. reflexivity. Qed.

(** With the help of that function, we can convert a type environment into a
    list of assumptions: *)

Definition assumptions_of_tenv (E : tenv) : list proposition :=
  map proposition_of_type (map snd E).

Example aot_XY :
  assumptions_of_tenv
    [("x"%string, tvar "X"); ("y"%string, tvar "Y")]
  =
    [atom "X"; atom "Y"].
Proof. reflexivity. Qed.

(** **** Exercise: 3 stars, standard (curry_howard) *)

(** Derivation of typability for a program also yields a derivation of
    provability for a proposition.*)

Theorem curry_howard : forall E e t,
  hastype E e t ->
  provable (assumptions_of_tenv E) (proposition_of_type t).
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

End Implicational.

(* ################################################################# *)
(** * Extending the Correspondence to Larger Systems *)

Module Propositional.

(* ================================================================= *)
(** ** Logic: Adding Conjunction and Disjunction *)

(** Now we extend the development to a full propositional logic with conjunction
    and disjunction. *)

Inductive proposition :=
  | atom (id : string)
  | implies (p q : proposition)
  | and (p q : proposition)
  | or (p q : proposition)
  | false.

Definition not (f : proposition) : proposition :=
  implies f false.

Definition true : proposition :=
  implies false false.

Definition iff (p q : proposition) :=
  and (implies p q) (implies q p).

(** The new proof system rules are as follows: *)

(**

        A |- p   A |- q
        --------------- (and intro)
          A |- p /\ q

        A |- p /\ q
        ----------- (and elim L)
          A |- p

        A |- p /\ q
        ----------- (and elim R)
          A |- q

          A |- p
        ----------- (or intro L)
        A |- p \/ q

          A |- q
        ----------- (or intro R)
        A |- p \/ q

        A, p |- r    A, q |- r    A |- p \/ q
        ------------------------------------- (or elim)
                      A |- r

*)

(** The rules:

    - And intro: to prove a conjunction, prove both parts.
    - And elim L: from a conjunction, obtain its first component.
    - And elim R: from a conjunction, obtain its second component.
    - Or intro L: to prove a disjunction, prove the left part.
    - Or intro R: to prove a disjunction, prove the right part.
    - Or elim: to use a disjunction, consider both cases and show a
      common conclusion follows. *)

(** We formalize those as follows. *)

Inductive provable : list proposition -> proposition -> Prop :=
  (* The first four rules were part of our previous development. *)
  | axiom : forall A p,
      In p A ->
      provable A p
  | implies_intro : forall A p q,
      provable (p :: A) q ->
      provable A (implies p q)
  | implies_elim : forall A p q,
      provable A (implies p q) ->
      provable A p ->
      provable A q
  | false_elim : forall A p,
      provable A false ->
      provable A p
  (* The next six rules are new. *)
  | and_intro : forall A p q,
      provable A p ->
      provable A q ->
      provable A (and p q)
  | and_elim_L : forall A p q,
      provable A (and p q) ->
      provable A p
  | and_elim_R : forall A p q,
      provable A (and p q) ->
      provable A q
  | or_intro_L : forall A p q,
      provable A p ->
      provable A (or p q)
  | or_intro_R : forall A p q,
      provable A q ->
      provable A (or p q)
  | or_elim : forall A p q r,
      provable (p :: A) r ->
      provable (q :: A) r ->
      provable A (or p q) ->
      provable A r.

(* ================================================================= *)
(** ** Programs: Adding Products, Sums, and the Empty Type *)

(** We extend the language with pairs, variants, and the empty type.

    - _Pairs_ combine two values; their type is a product [t1 * t2]. Projections
      [fst] and [snd] extract components.

    - _Variants_ represent a value of one of two types, written [t1 + t2],
      like this Rocq type:

        Inductive sum (T1 T2 : Type) :=
        | inl : T1 -> sum T1 T2
        | inr : T2 -> sum T1 T2.

      A [case] expression (like Rocq's [match]) analyzes them:

        case e of (x1 : t1) => e1 | (x2 : t2) => e2 end

    - The _empty type_ has no values and corresponds to [false]. The expression
      [magic t e] "magically" produces a value of type [t] from [e : empty].
      It is like an empty [match] expression in Rocq. *)

Inductive type :=
  | tvar (id : string)
  | arrow (t1 t2 : type)
  | product (t1 t2 : type)
  | sum (t1 t2 : type)
  | empty.

Inductive expr :=
  | var (id : string)
  | abs (id : string) (t : type) (e : expr)
  | app (e1 e2 : expr)
  | magic (t : type) (e : expr)
  | pair (e1 e2 : expr)
  | fst (e : expr)
  | snd (e : expr)
  | inl (e1 : expr)
  | inr (e2 : expr)
  | case (e : expr) (id1 : string) (t1 : type) (e1 : expr)
                    (id2 : string) (t2 : type) (e2 : expr).

(** The new type system rules are as follows: *)

(**

          E |- e : empty
        ------------------ (t-magic)
        E |- magic t e : t

        E |- e1 : t1    E |- e2 : t2
        ---------------------------- (t-pair)
        E |- pair e1 e2 : t1 * t2

        E |- e : t1 * t2
        ---------------- (t-fst)
        E |- fst e : t1

        E |- e : t1 * t2
        ---------------- (t-snd)
        E |- snd e : t2

              E |- e : t1
        -------------------- (t-inl)
        E |- inl e : t1 + t2

              E |- e : t2
        -------------------- (t-inr)
        E |- inr e : t1 + t2

        E |- e : t1 + t2   E, x1:t1 |- e1 : t   E, x2:t2 |- e2 : t
        ---------------------------------------------------------- (t-case)
        E |- case e of (x1 : t1) => e1 | (x2 : t2) => e2 end : t

*)

(** The rules:

    - T-Magic: from an impossible value, produce a value of any type.
    - T-Pair: combine two values into a pair.
    - T-Fst: from a pair, obtain its first component.
    - T-Snd: from a pair, obtain its second component.
    - T-Inl: inject a value into the left side of a sum.
    - T-Inr: inject a value into the right side of a sum.
    - T-Case: to use a sum, consider both cases and produce the same type. *)

(** We formalize those as follows. *)

Definition tenv := list (string * type).

Inductive hastype : tenv -> expr -> type -> Prop :=
  (* The first three rules were part of our previous development. *)
  | t_var : forall E x t,
      In (x, t) E ->
      hastype E (var x) t
  | t_abs : forall E x t1 e t2,
      hastype ((x, t1) :: E) e t2 ->
      hastype E (abs x t1 e) (arrow t1 t2)
  | t_app : forall E e1 t1 t2 e2,
      hastype E e1 (arrow t1 t2) ->
      hastype E e2 t1 ->
      hastype E (app e1 e2) t2
  (* The next seven rules are new. *)
  | t_magic : forall E e t,
      hastype E e empty ->
      hastype E (magic t e) t
  | t_pair : forall E e1 e2 t1 t2,
      hastype E e1 t1 ->
      hastype E e2 t2 ->
      hastype E (pair e1 e2) (product t1 t2)
  | t_fst : forall E e t1 t2,
      hastype E e (product t1 t2) ->
      hastype E (fst e) t1
  | t_snd : forall E e t1 t2,
      hastype E e (product t1 t2) ->
      hastype E (snd e) t2
  | t_inl : forall E e t1 t2,
      hastype E e t1 ->
      hastype E (inl e) (sum t1 t2)
  | t_inr : forall E e t1 t2,
      hastype E e t2 ->
      hastype E (inr e) (sum t1 t2)
  | t_case : forall E e x1 t1 e1 x2 t2 e2 t,
      hastype E e (sum t1 t2) ->
      hastype ((x1, t1) :: E) e1 t ->
      hastype ((x2, t2) :: E) e2 t ->
      hastype E (case e x1 t1 e1 x2 t2 e2) t.

(* ================================================================= *)
(** ** Proving the Extended Correspondence *)

(** The new rules we've added are also in a correspondence:

    - [false_elim] corresponds to [t_magic].
    - [and_intro] corresponds to [t_pair].
    - [and_elim_L] corresponds to [t_fst].
    - [and_elim_R] corresponds to [t_snd].
    - [or_intro_L] corresponds to [t_inl].
    - [or_intro_R] corresponds to [t_inr].
    - [or_elim] corresponds to [t_case].

    And therefore there is an extended correspondence between logical connectives
    and programming language features:

    - (_Propositional variables_ correspond to _program variables_.)
    - (_Implication_ corresponds to _functions and application_.)
    - _False_ corresponds to the _empty type_.
    - _Conjunction_ corresponds to _pairs_.
    - _Disjunction_ corresponds to _variants_.

    *)

(** Now we can re-prove the first of the two main Curry-Howard theorems for our
    extended logic and programming language. First, we extend our conversion
    function to change products to conjunctions, and sums to disjunctions. *)

Fixpoint proposition_of_type (t : type) : proposition :=
  match t with
  | tvar x => atom x
  | arrow t1 t2 =>
    implies (proposition_of_type t1) (proposition_of_type t2)
  | product t1 t2 =>
    and (proposition_of_type t1) (proposition_of_type t2)
  | sum t1 t2 =>
    or (proposition_of_type t1) (proposition_of_type t2)
  | empty => false
  end.

Definition assumptions_of_tenv (E : tenv) : list proposition :=
  map proposition_of_type (map Datatypes.snd E).

(** **** Exercise: 3 stars, standard (curry_howard_extended) *)

(** Derivation of typability for a program still yields a derivation of
    provability for a proposition. *)

Theorem curry_howard_extended : forall E e t,
  hastype E e t ->
  provable (assumptions_of_tenv E) (proposition_of_type t).
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * The Second Main Theorem of the Correspondence (Advanced) *)

(** So far: if a program is well-typed, its type-as-a-proposition is
    provable.

    Conversely: if a proposition is provable, there exists a well-typed
    program of that proposition-as-a-type.

    The forward direction erases programs; the converse must synthesize them. *)

(** First, we define a function that converts a proposition to a string
    representation. *)

Fixpoint string_of_proposition (p : proposition) : string :=
  match p with
  | atom id => "(" ++ id ++ ")"
  | implies p q =>
    "(implies " ++ (string_of_proposition p) ++ " "
                ++ (string_of_proposition q) ++ ")"
  | and p q =>
    "(and " ++ (string_of_proposition p) ++ " "
            ++ (string_of_proposition q) ++ ")"
  | or p q =>
    "(or " ++ (string_of_proposition p) ++ " "
           ++ (string_of_proposition q) ++ ")"
  | false => "(false)"
  end.

(** Second, we define a function that converts a proposition to
    its equivalent type. *)

Fixpoint type_of_proposition (p : proposition) : type :=
  match p with
  | atom id => tvar id
  | implies p q => arrow (type_of_proposition p) (type_of_proposition q)
  | and p q => product (type_of_proposition p) (type_of_proposition q)
  | or p q => sum (type_of_proposition p) (type_of_proposition q)
  | false => empty
  end.

(** Third, we define a function to convert assumptions to a type
    environment. Each assumption gets a name, which is its conversion
    to a string. *)

Definition tenv_of_assumptions (A : list proposition) : tenv :=
  map (fun p => (string_of_proposition p, type_of_proposition p)) A.

(** Now we're ready for the second of the main Curry-Howard theorems. *)

(** **** Exercise: 4 stars, advanced (curry_howard_converse) *)

(** Prove that if a proposition is provable, then there is a well-typed
    program whose type corresponds to that proposition. *)

Theorem curry_howard_converse : forall A p,
  provable A p ->
  exists e, hastype (tenv_of_assumptions A) e (type_of_proposition p).
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

End Propositional.

(* ################################################################# *)
(** * Further Extensions *)

(** The Curry–Howard correspondence extends far beyond this chapter.

    - Classical axioms ↔ control flow (e.g., exceptions)
    - Universal quantification ↔ dependent types
    - Existential quantification ↔ abstract types
    - Second-order quantification ↔ polymorphism

    These ideas underlie modern type systems, proof assistants, and
    program verification. *)

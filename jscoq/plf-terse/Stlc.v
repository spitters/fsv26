(** * Stlc: The Simply Typed Lambda-Calculus *)

(** Our job for this chapter: Formalize a small _functional_
    language and its type system.

    Language: The _simply typed lambda-calculus_ (STLC).
       - A small subset of Rocq's built-in functional language...
       - ...but we'll use different concrete syntax (to avoid
         confusion, and for consistency with standard treatments)

    Main new technical challenges:
      - variable binding
      - substitution

    The STLC lives in the lower-left front corner of the famous
    _lambda cube_ (also called the _Barendregt Cube_), which
    visualizes three sets of features that can be added to its
    simple core:

                               Calculus of Constructions
      type operators +--------+
                    /|       /|
                   / |      / |
     polymorphism +--------+  |
                  |  |     |  |
                  |  +-----|--+
                  | /      | /
                  |/       |/
                  +--------+ dependent types
                STLC

    Moving from bottom to top in the cube corresponds to adding
    _polymorphic types_ like [forall X, X -> X].  Adding _just_
    polymorphism gives us the famous Girard-Reynolds calculus, System F.

    Moving from front to back corresponds to adding _type operators_
    like [list].

    Moving from left to right corresponds to adding _dependent types_
    like [forall n, array-of-size n].

    The top right corner on the back, which combines all three features,
    is called the _Calculus of Constructions_.  First studied by
    Coquand and Huet, it forms the foundation of Rocq's logic. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".

(* ################################################################# *)
(** * Overview *)

(** Begin with some set of _base types_ (here, just [Bool])

    Add: variables, function abstractions, and applications *)

(** Informal concrete syntax:

       t ::= x                         (variable)
           | \x:T,t                    (abstraction)
           | t1 t2                     (application)
           | true                      (constant true)
           | false                     (constant false)
           | if t1 then t2 else t3     (conditional)
*)

(** Some examples:

      - [\x:Bool, x]

        The identity function for booleans.

      - [(\x:Bool, x) true]

        The identity function for booleans, applied to the boolean [true].

      - [\x:Bool, if x then false else true]

        The boolean "not" function.

      - [\x:Bool, true]

        The constant function that takes every (boolean) argument to
        [true].
      - [\x:Bool, \y:Bool, x]

        A two-argument function that takes two booleans and returns
        the first one. *)

(**   - [(\x:Bool, \y:Bool, x) false true]

        A two-argument function that takes two booleans and returns
        the first one, applied to the booleans [false] and [true]. *)

(**
      - [\f:Bool->Bool, f (f true)]

        A higher-order function that takes a _function_ [f] (from
        booleans to booleans) as an argument, applies [f] to [true],
        and applies [f] again to the result.

      - [(\f:Bool->Bool, f (f true)) (\x:Bool, false)]

        The same higher-order function, applied to the constantly
        [false] function. *)

(** Note that _all_ functions are anonymous.

    We'll see how to add named function declarations as "syntactic
    sugar" in the [MoreStlc] chapter.

    The _types_ of the STLC include the base type [Bool] for
    boolean values and arrow types for functions.

      T ::= Bool
          | T -> T
*)
(**
    For example:

      - [\x:Bool, false] has type [Bool->Bool]

      - [\x:Bool, x] has type [Bool->Bool]

      - [(\x:Bool, x) true] has type [Bool]

      - [\x:Bool, \y:Bool, x] has type [Bool->Bool->Bool]
                              (i.e., [Bool -> (Bool->Bool)])

      - [(\x:Bool, \y:Bool, x) false] has type [Bool->Bool]

      - [(\x:Bool, \y:Bool, x) false true] has type [Bool] *)

(* QUIZ

    What is the type of the following term?

       \f:Bool->Bool, f (f true)

    (A) [Bool -> (Bool -> Bool)]

    (B) [(Bool->Bool) -> Bool]

    (C) [Bool->Bool]

    (D) [Bool]

    (E) none of the above

*)
(* QUIZ

    How about the type of this one?

         (\f:Bool->Bool, f (f true)) (\x:Bool, false)

    (A) [Bool-> (Bool -> Bool)]

    (B) [(Bool->Bool) -> Bool]

    (C) [Bool->Bool]

    (D) [Bool]

    (E) none of the above

*)

(* ################################################################# *)
(** * Syntax *)

(** We next formalize the syntax of the STLC. *)

Module STLC.

(* ================================================================= *)
(** ** Types *)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

(* ================================================================= *)
(** ** Terms *)

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.

(** We need some notation magic to set up the concrete syntax, as
    we did in the [Imp] chapter... *)

Declare Scope stlc_scope.
Delimit Scope stlc_scope with stlc.
Open Scope stlc_scope.

Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.

Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.

Notation "<{{ x }}>" := x (x custom stlc_ty).

Notation "( t )" := t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 99, right associativity) : stlc_scope.

Notation "$( t )" := t (in custom stlc_ty at level 0, t constr) : stlc_scope.

Notation "'Bool'" := Ty_Bool (in custom stlc_ty at level 0) : stlc_scope.
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc_tm at level 200,
                    x custom stlc_tm,
                    y custom stlc_tm,
                    z custom stlc_tm at level 200,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc_tm at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc_tm at level 0).

(** We'll write types inside of [<{{ ... }}>] brackets: *)

Check <{{ Bool }}>.
Check <{{ Bool -> Bool }}>.
Check <{{ (Bool -> Bool) -> Bool }}>.

Notation "$( x )" := x (in custom stlc_tm at level 0, x constr, only parsing) : stlc_scope.
Notation "x" := x (in custom stlc_tm at level 0, x constr at level 0) : stlc_scope.
Notation "<{ e }>" := e (e custom stlc_tm at level 200) : stlc_scope.
Notation "( x )" := x (in custom stlc_tm at level 0, x custom stlc_tm) : stlc_scope.

Notation "x y" := (tm_app x y) (in custom stlc_tm at level 10, left associativity) : stlc_scope.
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc_tm at level 200, x global,
                     t custom stlc_ty,
                     y custom stlc_tm at level 200,
                     left associativity).
Coercion tm_var : string >-> tm.
Arguments tm_var _%_string.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

(** And terms inside of [<{ .. }>] brackets: *)

(** Examples... *)

Notation idB :=
  <{ \x:Bool, x }>.

Notation idBB :=
  <{ \x:Bool->Bool, x }>.

Notation idBBBB :=
  <{ \x: (Bool->Bool)->(Bool->Bool), x}>.

Notation k := <{ \x:Bool, \y:Bool, x }>.

Notation notB := <{ \x:Bool, if x then false else true }>.

(** Note that an abstraction [\x:T,t] (formally, [tm_abs x T t]) is
    always annotated with the type [T] of its parameter, in contrast
    to Rocq (and other functional languages like ML, Haskell, etc.),
    which use type inference to fill in missing annotations.  We're
    not considering type inference at all here. *)

(* ################################################################# *)
(** * Operational Semantics *)

(** To define the small-step semantics of STLC terms...

    - We begin by defining the set of values.

    - Next, we define _free variables_ and _substitution_.  These are
      used in the reduction rule for application expressions.

    - Finally, we give the small-step relation itself.
*)

(* ================================================================= *)
(** ** Values *)

(** To define the values of the STLC, we have a few cases to consider.

    First, for the boolean part of the language, the situation is
    clear: [true] and [false] are the only values.  An [if] expression
    is never a value. *)

(** Second, an application is not a value: it represents a function
    being invoked on some argument, which clearly still has work left
    to do. *)

(** Third, for abstractions, we have a choice:

      - We can say that [\x:T, t] is a value only when [t] is a
        value -- i.e., only if the function's body has been
        reduced (as much as it can be without knowing what argument it
        is going to be applied to).

      - Or we can say that [\x:T, t] is always a value, no matter
        whether [t] is one or not -- in other words, we can say that
        reduction stops at abstractions.

    Our usual way of evaluating expressions in Gallina makes the first
    choice -- for example,

         Compute (fun x:bool => 3 + 4)

    yields:

         fun x:bool => 7

    But Gallina is rather unusual in this respect.  Most functional
    programming languages make the second choice -- reduction of a
    function's body only begins when the function is actually applied
    to an argument.

    We also make the second choice here. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.

Hint Constructors value : core.

(* ================================================================= *)
(** ** STLC Programs *)

(** Finally, we must consider what constitutes a _complete_ program.

    Intuitively, a "complete program" must not refer to any undefined
    variables.  We'll see shortly how to define the _free_ variables
    in a STLC term.  A complete program, then, is one that is
    _closed_ -- that is, that contains no free variables.

    (Conversely, a term that may contain free variables is often
    called an _open term_.) *)

(** Having made the choice not to reduce under abstractions, we don't
    need to worry about whether variables are values, since we'll
    always be reducing programs "from the outside in," and that means
    the [step] relation will always be working with closed terms. *)

(* ================================================================= *)
(** ** Substitution *)

(** Now we come to the heart of the STLC: the operation of
    substituting one term for a variable in another term.  This
    operation is used below to define the operational semantics of
    function application, where we will need to substitute the
    argument term for the function parameter in the function's body.
    For example, we reduce

       (\x:Bool, if x then true else x) false

    to

       if false then true else false

    by substituting [false] for the parameter [x] in the body of the
    function.

    In general, we need to be able to substitute some given term [s]
    for occurrences of some variable [x] in another term [t].
    Informally, this is written [ [x:=s]t ] and pronounced "substitute
    [s] for [x] in [t]." *)

(** Here are some examples:

      - [[x:=true] (if x then true else false)]
           yields [if true then true else false]

      - [[x:=true] x] yields [true]

      - [[x:=true] (if x then x else y)] yields [if true then true else y]

      - [[x:=true] y] yields [y]

      - [[x:=true] false] yields [false] (vacuous substitution)

      - [[x:=true] (\y:Bool, if y then x else false)]
           yields [\y:Bool, if y then true else false]

      - [[x:=true] (\y:Bool, x)] yields [\y:Bool, true]

      - [[x:=true] (\y:Bool, y)] yields [\y:Bool, y]

      - [[x:=true] (\x:Bool, x)] yields [\x:Bool, x]

    The last example is key: substituting [x] with [true] in
    [\x:Bool, x] does _not_ yield [\x:Bool, true]!  The reason for
    this is that the [x] in the body of [\x:Bool, x] is _bound_ by the
    abstraction: it is a new, local name that just happens to be
    spelled the same as some global name [x]. *)

(** Here is the definition, informally...

       [x:=s]x               = s
       [x:=s]y               = y                     if x <> y
       [x:=s](\x:T, t)       = \x:T, t
       [x:=s](\y:T, t)       = \y:T, [x:=s]t         if x <> y
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)
       [x:=s]true            = true
       [x:=s]false           = false
       [x:=s](if t1 then t2 else t3) =
                       if [x:=s]t1 then [x:=s]t2 else [x:=s]t3
*)

(** ... and formally: *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{[x:=s] t1 [x:=s] t2}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if [x:=s] t1 then [x:=s] t2 else [x:=s] t3}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm).

(* QUIZ

    What is the result of the following substitution?

       [x:=s](\y:T1, x (\x:T2, x))

    (1) [(\y:T1, x (\x:T2, x))]

    (2) [(\y:T1, s (\x:T2, s))]

    (3) [(\y:T1, s (\x:T2, x))]

    (4) none of the above

*)

(** _Technical note_: Substitution also becomes trickier to define if
    we consider the case where [s], the term being substituted for a
    variable in some other term, may itself contain free variables. *)

(** Here is an example of how things would become trickier if one were
    to substitute _open_ terms. Using the simple definition of
    substitution above to substitute the open term

      s = \x:Bool, r

    (where [r] is a _free_ reference to some global resource) for
    the free variable [z] in the term

      t = \r:Bool, z

    where [r] is a bound variable, we would get

      \r:Bool, \x:Bool, r

    where the free reference to [r] in [s] has been "captured" by
    the binder at the beginning of [t]. *)

(** Why would this be bad?  Because it violates the principle that the
    names of bound variables do not matter.  For example, if we rename
    the bound variable in [t], e.g., let

      t' = \w:Bool, z

    then [[z:=s]t'] is

      \w:Bool, \x:Bool, r

    which does not behave the same as the substituting in the original t:

      [z:=s]t = \r:Bool, \x:Bool, r

    That is, renaming a bound variable in [t] would change how [t]
    behaves under our simple substitution. So substitution gets more
    complicated in that setting, but fortunately we don't have that
    problem in our STLC variant. *)

(** Fortunately, since we are only interested here in defining the
    [step] relation on _closed_ terms (i.e., terms like [\x:Bool, x]
    that include binders for all of the variables they mention), we
    can sidestep this extra complexity, but it must be dealt with when
    formalizing richer languages. *)

(* ================================================================= *)
(** ** Reduction *)

(**
                              value v
                       -----------------------                      (ST_AppAbs)
                       (\x:T,t) v --> [x:=v]t

                              t1 --> t1'
                           ----------------                           (ST_App1)
                           t1 t2 --> t1' t2

                              value v1
                              t2 --> t2'
                           ----------------                           (ST_App2)
                           v1 t2 --> v1 t2'
*)
(** (plus the usual rules for conditionals). *)

(** The [ST_AppAbs] rule is often called _beta-reduction_. *)

(** This is _call by value_ reduction: to reduce an
    application [(t1 t2)], we
      - first reduce [t1] to a value: a function [\x:T,t]
      - then reduce the argument [t2] to a value [v]
      - then reduce the application itself by substituting [v] for
        the bound variable [x] in the body [t]. *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t v,
         value v ->
         <{(\x:T, t) v}> --> <{ [x:=v]t }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
(* QUIZ

    What does the following term step to?

    (\x:Bool->Bool, x) (\x:Bool, x) --> ???

(A) [ \x:Bool, x ]

(B) [ \x:Bool->Bool, x ]

(C) [ (\x:Bool->Bool, x) (\x:Bool, x) ]

(D) none of the above

*)
(* QUIZ

    What does the following term step to?

   (\x:Bool->Bool, x)
       ((\x:Bool->Bool, x) (\x:Bool, x))
   --> ???

(A) [ \x:Bool, x ]

(B) [ \x:Bool->Bool, x ]

(C) [ (\x:Bool->Bool, x) (\x:Bool, x) ]

(D) [ (\x:Bool->Bool, x) ((\x:Bool->Bool, x) (\x:Bool, x)) ]

(E) none of the above

*)
(* QUIZ

    What does the following term _normalize_ to?

   (\x:Bool->Bool, x) notB true  -->* ???

where [notB] abbreviates [\x:Bool, if x then false else true]

(A) [ \x:Bool, x ]

(B) [ true ]

(C) [ false ]

(D) [ notB ]

(E) none of the above

*)
(* QUIZ

    What does the following term normalize to?

  (\x:Bool, x) (notB true) -->* ???

(A) [ \x:Bool, x ]

(B) [ true ]

(C) [ false ]

(D) [ notB true ]

(E) none of the above

*)

(* ================================================================= *)
(** ** Examples *)

(** Example:

      (\x:Bool->Bool, x) (\x:Bool, x) -->* \x:Bool, x

    i.e.,

      idBB idB -->* idB
*)

Lemma step_example1 :
  <{idBB idB}> -->* idB.
Proof.
  eapply multi_step.
  - apply ST_AppAbs.
    apply v_abs.
  - simpl.
    apply multi_refl.  Qed.

(** Example:

      (\x:Bool->Bool, x) ((\x:Bool->Bool, x) (\x:Bool, x))
            -->* \x:Bool, x

    i.e.,

      (idBB (idBB idB)) -->* idB.
*)

Lemma step_example2 :
  <{idBB (idBB idB)}> -->* idB.
Proof.
  eapply multi_step.
  - apply ST_App2.
    + auto.
    + apply ST_AppAbs. auto.
  - eapply multi_step.
    + apply ST_AppAbs. simpl. auto.
    + simpl. apply multi_refl.  Qed.

(** Example:

      (\x:Bool->Bool, x)
         (\x:Bool, if x then false else true)
         true
            -->* false

    i.e.,

       (idBB notB) true -->* false.
*)

Lemma step_example3 :
  <{idBB notB true}> -->* <{false}>.
Proof.
  eapply multi_step.
  - apply ST_App1. apply ST_AppAbs. auto.
  - simpl. eapply multi_step.
    + apply ST_AppAbs. auto.
    + simpl. eapply multi_step.
      * apply ST_IfTrue.
      * apply multi_refl.  Qed.

(** Example:

      (\x:Bool -> Bool, x)
         ((\x:Bool, if x then false else true) true)
            -->* false

    i.e.,

      idBB (notB true) -->* false.

    (Note that this term doesn't actually typecheck; even so, we can
    ask how it reduces.)
*)

Lemma step_example4 :
  <{idBB (notB true)}> -->* <{false}>.
Proof.
  eapply multi_step.
  - apply ST_App2; auto.
  - eapply multi_step.
    + apply ST_App2; auto.
      apply ST_IfTrue.
    + eapply multi_step.
      * apply ST_AppAbs. auto.
      * simpl. apply multi_refl.  Qed.

(* QUIZ

    Do values and normal forms coincide in the language presented so far?

    (A) yes

    (B) no

*)

(* ################################################################# *)
(** * Typing *)

(** Next we consider the typing relation of the STLC, which is
    meant to prevent reduction from getting stuck. *)

(* ================================================================= *)
(** ** Contexts *)

(** _Question_: What is the type of the term "[x y]"?

    _Answer_: It depends on the types of [x] and [y]!

    I.e., in order to assign a type to a term, we need to know
    what assumptions we should make about the types of its free
    variables.

    This leads us to a three-place _typing judgment_, informally
    written [Gamma |-- t \in T], where [Gamma] is a
    "typing context" -- a mapping from variables to their types. *)

Definition context := partial_map ty.

(** Following the usual notation for partial maps, we write
    [(x |-> T, Gamma)] for "update the partial function [Gamma] so
    that it maps [x] to [T]." *)

(* ================================================================= *)
(** ** Typing Relation *)

(**
                            Gamma x = T1
                          ------------------                             (T_Var)
                          Gamma |-- x \in T1

                      x |-> T2 ; Gamma |-- t1 \in T1
                      ------------------------------                     (T_Abs)
                       Gamma |-- \x:T2,t1 \in T2->T1

                        Gamma |-- t1 \in T2->T1
                          Gamma |-- t2 \in T2
                         ----------------------                          (T_App)
                         Gamma |-- t1 t2 \in T1

                         -----------------------                         (T_True)
                         Gamma |-- true \in Bool

                         ------------------------                       (T_False)
                         Gamma |-- false \in Bool

    Gamma |-- t1 \in Bool    Gamma |-- t2 \in T    Gamma |-- t3 \in T
    -----------------------------------------------------------------    (T_If)
                  Gamma |-- if t1 then t2 else t3 \in T

    We can read the three-place relation [Gamma |-- t \in T] as:
    "under the assumptions in Gamma, the term [t] has the type [T]." *)

(** In the formal development, we write this judgment in
    [<{ .. }>] brackets. *)



Notation "x '|->' v ';' m " := (update m x v)
  (in custom stlc_tm at level 0, x constr at level 0, v  custom stlc_ty, right associativity) : stlc_scope.

Notation "x '|->' v " := (update empty x v)
  (in custom stlc_tm at level 0, x constr at level 0, v custom stlc_ty) : stlc_scope.

Notation "'empty'" := empty (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
            (at level 0, Gamma custom stlc_tm at level 200, t custom stlc_tm, T custom stlc_ty).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      <{ Gamma |-- x \in T1 }>
  | T_Abs : forall Gamma x T1 T2 t1,
      <{ x |-> T2 ; Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- \x:T2, t1 \in T2 -> T1 }>
  | T_App : forall T1 T2 Gamma t1 t2,
      <{ Gamma |-- t1 \in T2 -> T1 }> ->
      <{ Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- t1 t2 \in T1 }>
  | T_True : forall Gamma,
      <{ Gamma |-- true \in Bool }>
  | T_False : forall Gamma,
      <{ Gamma |-- false \in Bool }>
  | T_If : forall t1 t2 t3 T1 Gamma,
       <{ Gamma |-- t1 \in Bool }> ->
       <{ Gamma |-- t2 \in T1 }> ->
       <{ Gamma |-- t3 \in T1 }> ->
       <{ Gamma |-- if t1 then t2 else t3 \in T1 }>

where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T) : stlc_scope.

Hint Constructors has_type : core.

(* ================================================================= *)
(** ** Examples *)

Example typing_example_1 :
  <{ empty |-- \x:Bool, x \in Bool -> Bool }>.
Proof. eauto. Qed.

(** Note that, since we added the [has_type] constructors to the hints
    database, [eauto] can solve this one immediately. *)

(** More examples:

       empty |-- \x:Bool, \y:Bool->Bool, y (y x)
             \in Bool -> (Bool->Bool) -> Bool.
*)

Example typing_example_2 :
  <{ empty |--
    \x:Bool,
       \y:Bool->Bool,
          (y (y x)) \in
    Bool -> (Bool -> Bool) -> Bool }>.
Proof. eauto 20. Qed.

(**
    exists T,
       empty |-- \x:Bool->Bool, \y:Bool->Bool, \z:Bool,
                   y (x z)
             \in T.
*)

(** We can also show that some terms are _not_ typable.  For example,
    we can check that there is no typing derivation assigning a type
    to the term [\x:Bool, \y:Bool, x y] -- i.e.,

    ~ exists T,
        empty |-- \x:Bool, \y:Bool, x y \in T.
*)

Example typing_nonexample_1 :
  ~ exists T,
    <{  empty |--
        \x:Bool,
            \y:Bool,
               (x y) \in
        T }>.
Proof.
  intros Hc. destruct Hc as [T Hc].
  (* The [clear] tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion Hc; subst; clear Hc.
  inversion H4; subst; clear H4.
  inversion H5; subst; clear H5 H4.
  inversion H2; subst; clear H2.
  discriminate H1.
Qed.

(** Another nonexample:

    ~ (exists S T,
          empty |-- \x:S, x x \in T).
*)

(* QUIZ

    Which of the following propositions is _not_ provable?

    (A) [y:Bool |-- \x:Bool, x \in Bool->Bool]

    (B) [exists T,  empty |-- \y:Bool->Bool, \x:Bool, y x \in T]

    (C) [exists T,  empty |-- \y:Bool->Bool, \x:Bool, x y \in T]

    (D) [exists S, x:S |-- \y:Bool->Bool, y x \in (Bool->Bool)->S]

*)
(* QUIZ

    Which of these is not provable?

    (A) [exists T,  empty |-- \y:Bool->Bool->Bool, \x:Bool, y x \in T]

    (B) [exists S T,  x:S |-- x x x \in T]

    (C) [exists S U T,  x:S, y:U |-- \z:Bool, x (y z) \in T]

    (D) [exists S T,  x:S |-- \y:Bool, x (x y) \in T]

*)
End STLC.


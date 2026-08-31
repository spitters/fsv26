(** * MoreStlc: More on the Simply Typed Lambda-Calculus *)

Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.

(* ################################################################# *)
(** * Simple Extensions to STLC *)

(** The simply typed lambda-calculus has a rich enough structure to make
    its theoretical properties interesting, but it is not much of a
    programming language!

    In this chapter, we begin to close the gap with real-world languages by
    introducing a number of familiar features that have straightforward
    treatments at the level of typing. *)

(* ================================================================= *)
(** ** Numbers *)

(** Adding types, constants, and primitive operations for
    natural numbers is easy (as we saw in the [STLCArith] exercises). *)

(* ================================================================= *)
(** ** Let Bindings *)

(** A more interesting extension... let-bindings.

    When writing a complex expression, it is often useful to give
    names to some of its subexpressions: this avoids repetition and
    often increases readability. *)

(** Syntax:

       t ::=                Terms
           | ...               (other terms same as before)
           | let x=t1 in t2    let-binding
*)

(**
    Reduction:

                                 t1 --> t1'
                     ----------------------------------               (ST_Let1)
                     let x=t1 in t2 --> let x=t1' in t2

                        ----------------------------              (ST_LetValue)
                        let x=v1 in t2 --> [x:=v1]t2

    Typing:

             Gamma |-- t1 \in T1      x|->T1; Gamma |-- t2 \in T2
             ----------------------------------------------------      (T_Let)
                        Gamma |-- let x=t1 in t2 \in T2
*)

(* ================================================================= *)
(** ** Pairs *)

(** In Rocq, the primitive way of extracting the components of a pair
    is _pattern matching_.  An alternative is to take [fst] and
    [snd] -- the first- and second-projection operators -- as
    primitives.  Just for fun, let's do our pairs this way.  For
    example, here's how we'd write a function that takes a pair of
    numbers and returns the pair of their sum and difference:

       \x : Nat*Nat,
          let sum = x.fst + x.snd in
          let diff = x.fst - x.snd in
          (sum,diff)
*)

(** Syntax:

       t ::=                Terms
           | ...
           | (t1,t2)           pair
           | t0.fst            first projection
           | t0.snd            second projection

       v ::=                Values
           | ...
           | (v1,v2)           pair value

       T ::=                Types
           | ...
           | T1 * T2           product type
*)

(** Reduction...

                              t1 --> t1'
                         --------------------                        (ST_Pair1)
                         (t1,t2) --> (t1',t2)

                              t2 --> t2'
                         --------------------                        (ST_Pair2)
                         (v1,t2) --> (v1,t2')

                               t0 --> t0'
                           ------------------                        (ST_Fst1)
                           t0.fst --> t0'.fst

                          ------------------                       (ST_FstPair)
                          (v1,v2).fst --> v1

                               t0 --> t0'
                           ------------------                        (ST_Snd1)
                           t0.snd --> t0'.snd

                          ------------------                       (ST_SndPair)
                          (v1,v2).snd --> v2
*)

(** Typing:

              Gamma |-- t1 \in T1     Gamma |-- t2 \in T2
              -------------------------------------------              (T_Pair)
                      Gamma |-- (t1,t2) \in T1*T2

                        Gamma |-- t0 \in T1*T2
                        -----------------------                        (T_Fst)
                        Gamma |-- t0.fst \in T1

                        Gamma |-- t0 \in T1*T2
                        -----------------------                        (T_Snd)
                        Gamma |-- t0.snd \in T2
*)

(* ================================================================= *)
(** ** Unit *)

(** Another handy base type, found especially in functional languages,
    is the singleton type [Unit]. *)

(** Syntax:

       t ::=                Terms
           | ...               (other terms same as before)
           | unit              unit

       v ::=                Values
           | ...
           | unit              unit value

       T ::=                Types
           | ...
           | Unit              unit type

    Typing:

                         -----------------------                       (T_Unit)
                         Gamma |-- unit \in Unit
*)

(* QUIZ

    Is [unit] the only term of type [Unit]?

    (A) Yes

    (B) No
*)

(** No! For instance (\x:Unit,x) unit is also a _term_ of type unit. *)

(* ================================================================= *)
(** ** Sums *)

(** Many programs need to deal with values that can take two distinct
   forms.  For example, we might identify students in a university
   database using _either_ their name _or_ their id number. A search
   function might return _either_ a matching value _or_ an error code.

   These are specific examples of a binary _sum type_ (sometimes called
   a _disjoint union_), which describes a set of values drawn from
   one of two given types, e.g.:

       Nat + Bool
*)
(**

    We create elements of these types by tagging elements of the
    component types, telling on which side of the sum we are putting
    them. E.g.,

   inl 42   \in Nat + Bool
   inr true \in Nat + Bool
*)

(** In general, the elements of a type [T1 + T2] consist of the
    elements of [T1] tagged with the token [inl], plus the elements of
    [T2] tagged with [inr]. *)

(** As we've seen in Rocq programming, one important use of sums is
    signaling errors:

      div \in Nat -> Nat -> (Nat + Unit)
      div =
        \x:Nat, \y:Nat,
          if iszero y then
            inr unit
          else
            inl ...
*)

(** Values of sum type are "destructed" by case analysis:

    getNat \in Nat+Bool -> Nat
    getNat =
      \x:Nat+Bool,
        case x of
          inl n => n
        | inr b => if b then 1 else 0
*)

(** Syntax:

       t ::=                Terms
           | ...               (other terms same as before)
           | inl T2 t1         tagging (left)
           | inr T1 t2         tagging (right)
           | case t0 of        case analysis
               inl x1 => t1
             | inr x2 => t2

       v ::=                Values
           | ...
           | inl T2 v1         tagged value (left)
           | inr T1 v2         tagged value (right)

       T ::=                Types
           | ...
           | T1 + T2           sum type
*)

(** Reduction:

                               t1 --> t1'
                        ------------------------                       (ST_Inl)
                        inl T2 t1 --> inl T2 t1'

                               t2 --> t2'
                        ------------------------                       (ST_Inr)
                        inr T1 t2 --> inr T1 t2'

                               t0 --> t0'
               -------------------------------------------            (ST_Case)
                case t0 of inl x1 => t1 | inr x2 => t2 -->
               case t0' of inl x1 => t1 | inr x2 => t2

            -----------------------------------------------        (ST_CaseInl)
            case (inl T2 v1) of inl x1 => t1 | inr x2 => t2
                           -->  [x1:=v1]t1

            -----------------------------------------------        (ST_CaseInr)
            case (inr T1 v2) of inl x1 => t1 | inr x2 => t2
                           -->  [x2:=v2]t2
*)

(** Typing:

                          Gamma |-- t1 \in T1
                   -------------------------------                      (T_Inl)
                   Gamma |-- inl T2 t1 \in T1 + T2

                          Gamma |-- t2 \in T2
                   --------------------------------                     (T_Inr)
                    Gamma |-- inr T1 t2 \in T1 + T2

                        Gamma |-- t0 \in T1+T2
                     x1|->T1; Gamma |-- t1 \in T3
                     x2|->T2; Gamma |-- t2 \in T3
         -------------------------------------------------------        (T_Case)
         Gamma |-- case t0 of inl x1 => t1 | inr x2 => t2 \in T3

    We use the type annotations on [inl] and [inr] to make the typing
    relation deterministic (each term has at most one type), as we
    did for functions. *)

(* QUIZ

    What does the following term step to (in one step)?

      let f = \x : Nat + Bool,
         case x of
           inl n => n + 3
           | inr b => 0 in
      f (inl Bool 4)


    (A)  (\x : Nat + Bool,
            case x of
              inl n => n + 3
              | inr b => 0
         ) (inl Bool 4)


    (B) 7


    (C)  case inl Bool 4 of
           inl n => n + 3
         | inr b => 0



    (D) f (inl Bool 4)

*)
(* QUIZ

    What about this one?

  (\x : Nat + Bool,
     case x of
     inl n => n + 3
     | inr b => 0
  ) (inl Bool 4)


   (A)  7


   (B)  case inl Bool 4 of
          inl n => n + 3
        | inr b => 0


   (C)  4 + 3

*)
(* QUIZ

    What about this one?

       case inl Bool 4 of
         inl n => n + 3
         | inr b => 0

   (A)  4 + 3

   (B)  7

   (C)  0
*)

(* ================================================================= *)
(** ** Lists *)

(**
    Syntax:

       t ::=                Terms
           | ...
           | nil T             empty list
           | t1 :: t2          cons
           | case t1 of        case analysis
               nil      => t2
               | xh::xt => t3

       v ::=                Values
           | ...
           | nil T             nil value
           | v1 :: v2          cons value

       T ::=                Types
           | ...
           | List T            list of Ts
*)

(** Reduction:

                                t1 --> t1'
                       --------------------------                    (ST_Cons1)
                         t1 :: t2 --> t1' :: t2

                                t2 --> t2'
                       --------------------------                    (ST_Cons2)
                         v1 :: t2 --> v1 :: t2'

                              t1 --> t1'
                -------------------------------------------         (ST_Lcase1)
                 (case t1 of nil => t2 | xh::xt => t3) -->
                (case t1' of nil => t2 | xh::xt => t3)

               ------------------------------------------          (ST_LcaseNil)
               (case nil T1 of nil => t2 | xh::xt => t3)
                                --> t2

              -------------------------------------------         (ST_LcaseCons)
              (case (vh::vt) of nil => t2 | xh::xt => t3)
                          --> [xh:=vh][xt:=vt]t3
*)

(** Typing:

                        ----------------------------                    (T_Nil)
                        Gamma |-- nil T1 \in List T1

            Gamma |-- t1 \in T1      Gamma |-- t2 \in List T1
            -------------------------------------------------           (T_Cons)
                    Gamma |-- t1 :: t2 \in List T1

                        Gamma |-- t1 \in List T1
                        Gamma |-- t2 \in T2
                (xh|->T1; xt|->List T1; Gamma) |-- t3 \in T2
          ----------------------------------------------------         (T_Lcase)
          Gamma |-- (case t1 of nil => t2 | xh::xt => t3) \in T2
*)

(* ================================================================= *)
(** ** General Recursion *)

(** Another facility found in most programming languages (including
    Rocq) is the ability to define recursive functions.  For example,
    we would like to be able to define and use the factorial function
    like this:

      let fact = \x:Nat,
                   if x=0 then 1 else x * (fact (pred x))) in
      fact 3.

   Note that the right-hand side of this binder mentions [fact], the
   variable being bound -- something that is not allowed according
   to the way we defined [let] above. *)

(** Extending our formalization of [let]s to handle "recursive
    definitions" would require non-trivial effort. *)

(** Here is another way of presenting recursive functions that is
    a bit more verbose but equally powerful and much more straightforward
    to formalize: instead of writing recursive definitions, we will define
    a _fixed-point operator_ called [fix] that performs the "unfolding"
    of the recursive definition in the right-hand side as needed, during
    reduction.

    For example, instead of

      fact = \x:Nat,
                if x=0 then 1 else x * (fact (pred x)))

    we will write:

      fact =
          fix
            (\f:Nat->Nat,
               \x:Nat,
                  if x=0 then 1 else x * (f (pred x)))
*)

(** Syntax:

       t ::=                Terms
           | ...
           | fix t1            fixed-point operator

   Reduction:

                                t1 --> t1'
                            ------------------                     (ST_Fix1)
                            fix t1 --> fix t1'

               --------------------------------------------      (ST_FixAbs)
               fix (\xf:T1.t1) --> [xf:=fix (\xf:T1.t1)] t1

   Typing:

                           Gamma |-- t1 \in T1->T1
                           -----------------------                    (T_Fix)
                           Gamma |-- fix t1 \in T1
*)

(** Let's see how [ST_FixAbs] works by reducing [fact 3 = fix F 3],
    where

    F = (\f. \x. if x=0 then 1 else x * (f (pred x)))

    (type annotations are omitted for brevity).

    fix F 3

[-->] [ST_FixAbs] + [ST_App1]

    (\x. if x=0 then 1 else x * (fix F (pred x))) 3

[-->] [ST_AppAbs]

    if 3=0 then 1 else 3 * (fix F (pred 3))

[-->] [ST_If0_Nonzero]

    3 * (fix F (pred 3))

[-->] [ST_FixAbs + ST_Mult2 + ST_App1]

    3 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 3))

[-->] [ST_PredNat + ST_Mult2 + ST_App2]

    3 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 2)

[-->] [ST_AppAbs + ST_Mult2]

    3 * (if 2=0 then 1 else 2 * (fix F (pred 2)))

[-->] [ST_If0_Nonzero + ST_Mult2]

    3 * (2 * (fix F (pred 2)))

[-->] [ST_FixAbs + 2 x ST_Mult2 + ST_App1]

    3 * (2 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 2)))

[-->] [ST_PredNat + 2 x ST_Mult2 + ST_App2]

    3 * (2 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 1))

[-->] [ST_AppAbs + 2 x ST_Mult2]

    3 * (2 * (if 1=0 then 1 else 1 * (fix F (pred 1))))

[-->] [ST_If0_Nonzero + 2 x ST_Mult2]

    3 * (2 * (1 * (fix F (pred 1))))

[-->] [ST_FixAbs + 3 x ST_Mult2 + ST_App1]

    3 * (2 * (1 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 1))))

[-->] [ST_PredNat + 3 x ST_Mult2 + ST_App2]

    3 * (2 * (1 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 0)))

[-->] [ST_AppAbs + 3 x ST_Mult2]

    3 * (2 * (1 * (if 0=0 then 1 else 0 * (fix F (pred 0)))))

[-->] [ST_If0Zero + 3 x ST_Mult2]

    3 * (2 * (1 * 1))

[-->] [ST_MultNats + 2 x ST_Mult2]

    3 * (2 * 1)

[-->] [ST_MultNats + ST_Mult2]

    3 * 2

[-->] [ST_MultNats]

    6
*)

(** The simply typed lambda-calculus with fixed points is a famous and
    extensively studied system. It is often called _PCF_ because it is a
    simple language of "partial computable functions". *)

(** One important point to note is that, unlike [Fixpoint]
    definitions in Rocq, there is nothing to prevent functions defined
    using [fix] from diverging. *)

(* QUIZ

    Is this a well-typed Stlc term? What does it evaluate to?

        fix (\f: Nat->Nat, \x:Nat, f x) 0

   (A) no

   (B) yes, diverges

   (C) yes, [42]

   (D) yes, [0]
*)
(* QUIZ

    Which of the following are (intuitively) true for Stlc + fixpoints.

   (A) deterministic

   (B) progress

   (C) preservation

   (D) normalizing (i.e. every well-typed term reduces to a normal form)
*)

(* ================================================================= *)
(** ** Records *)

(** As a final example, records can be presented as a
    generalization of pairs:
       - they are n-ary (rather than binary);
       - they are accessed by _label_ (rather than position). *)

(** Syntax:

       t ::=                          Terms
           | ...
           | {i1=t1, ..., in=tn}         record
           | t0.i                        projection

       v ::=                          Values
           | ...
           | {i1=v1, ..., in=vn}         record value

       T ::=                          Types
           | ...
           | {i1:T1, ..., in:Tn}         record type
*)

(** Note that this is a quite informal definition compared to
    previous ones:

    - it uses "[...]" in the syntax for records
    - it omits a usual side condition that the labels of a record should
      not contain repetitions. *)

(**
   Reduction:

                              ti --> ti'
                 ------------------------------------                  (ST_Rcd)
                     {i1=v1, ..., im=vm, in=ti , ...}
                 --> {i1=v1, ..., im=vm, in=ti', ...}

                              t0 --> t0'
                            --------------                           (ST_Proj1)
                            t0.i --> t0'.i

                      -------------------------                    (ST_ProjRcd)
                      {..., i=vi, ...}.i --> vi
*)

(**
    - In the first rule, [ti] must be the leftmost field that is not a value;
    - In the last rule, there should be only one field called [i],
      and all the other fields must contain values. *)

(** The typing rules are also simple:

            Gamma |-- t1 \in T1     ...     Gamma |-- tn \in Tn
          -----------------------------------------------------        (T_Rcd)
          Gamma |-- {i1=t1, ..., in=tn} \in {i1:T1, ..., in:Tn}

                    Gamma |-- t0 \in {..., i:Ti, ...}
                    ---------------------------------                  (T_Proj)
                          Gamma |-- t0.i \in Ti
*)

(** Formalizing all this takes some work.  See the [Records]
    chapter for details. *)


(* ################################################################# *)
(** * Exercise: Formalizing the Extensions *)

(** In this series of exercises, you will formalize some of the
    extensions described in this chapter.  We've provided the
    necessary additions to the syntax of terms and types, and we've
    included a few examples that you can test your definitions with to
    make sure they are working as expected.  You'll fill in the rest
    of the definitions and extend all the proofs accordingly.

    To get you started, we've provided implementations for:
     - numbers
     - sums
     - lists
     - unit

    You need to complete the implementations for:
     - pairs
     - let (which involves binding)
     - fix

    A good strategy is to work on the extensions one at a time (first
    pairs, then let, then fix), in separate passes, rather than trying
    to do all three at once in a single pass.  For each definition or
    proof, begin by reading carefully through the parts that are
    provided for you, referring to the text in the [Stlc] chapter
    for high-level intuitions and the embedded comments for detailed
    mechanics. *)


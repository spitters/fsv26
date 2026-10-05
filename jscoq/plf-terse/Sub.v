(** * Sub: Subtyping *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".

(* ################################################################# *)
(** * Concepts *)

(* ================================================================= *)
(** ** A Motivating Example *)

(** Suppose we are writing a program involving two record types
    defined as follows:

      Person  = {name:String, age:Nat}
      Student = {name:String, age:Nat, gpa:Nat}
*)

(** _Problem_: In the pure STLC with records, the following term is not
    typable:

    (\r:Person, (r.age)+1) {name="Pat",age=21,gpa=1}

    This is a shame. *)

(** _Idea_: Introduce _subtyping_, formalizing the observation that
    "some types are better than others." *)

(** Safe substitution principle:

       - [S] is a subtype of [T], written [S <: T], if a value of type
         [S] can safely be used in any context where a value of type
         [T] is expected.
*)

(* ================================================================= *)
(** ** Subtyping and Object-Oriented Languages *)

(** Subtyping plays a fundamental role in OO programming
    languages.

    Roughly, an _object_ can be thought of as a record of
    functions ("methods") and data values ("fields" or "instance
    variables").

       - Invoking a method [m] of an object [o] on some arguments
         [a1..an] consists of projecting out the [m] field of [o] and
         applying it to [a1..an].

    The type of an object is a _class_ (or an _interface_).

    Classes are related by the _subclass_ relation.

       - An object belonging to a subclass must provide all the
         methods and fields of one belonging to a superclass, plus
         possibly some more.

       - Thus a subclass object can be used anywhere a superclass
         object is expected.

       - Very handy for organizing large libraries

    Of course, real OO languages have lots of other features...
       - mutable fields
       - "private" and other visibility modifiers
       - method inheritance
       - static components
       - etc., etc.

    We'll ignore all these and focus on core mechanisms. *)

(* ================================================================= *)
(** ** The Subsumption Rule *)

(** Our goal for this chapter is to add subtyping to the simply typed
    lambda-calculus (with some of the basic extensions from [MoreStlc]).
    This involves two steps:

      - Defining a binary _subtype relation_ between types.

      - Enriching the typing relation to take subtyping into account.

    The second step is actually very simple.  We add just a single rule
    to the typing relation: the so-called _rule of subsumption_:

                         Gamma |-- t1 \in T1     T1 <: T2
                         --------------------------------           (T_Sub)
                               Gamma |-- t1 \in T2

    This rule says, intuitively, that it is OK to "forget" some of
    what we know about a term. *)

(* ================================================================= *)
(** ** The Subtype Relation *)

(** The first step -- the definition of the relation [S <: T] -- is
    where all the action is.  Let's look at each of the clauses of its
    definition.  *)

(* ----------------------------------------------------------------- *)
(** *** Structural Rules *)

(** To start off, we impose two "structural rules" that are
    independent of any particular type constructor: a rule of
    _transitivity_, which says intuitively that, if [S] is
    better (richer, safer) than [U] and [U] is better than [T],
    then [S] is better than [T]...

                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T

    ... and a rule of _reflexivity_, since certainly any type [T] is
    as good as itself:

                                   ------                              (S_Refl)
                                   T <: T
*)

(* ----------------------------------------------------------------- *)
(** *** Products *)

(** Now we consider the individual type constructors, one by one,
    beginning with product types.  We consider one pair to be a subtype
    of another if each of its components is.

                            S1 <: T1    S2 <: T2
                            --------------------                        (S_Prod)
                             S1 * S2 <: T1 * T2
*)

(* ----------------------------------------------------------------- *)
(** *** Arrows *)

(** Suppose we have functions [f] and [g] with these types:

       f : C -> Student
       g : (C->Person) -> D

    Is it safe to allow the application [g f]?

    Yes.

    So we want:

      C->Student  <:  C->Person

    I.e., arrow is _covariant_ in its right-hand argument. *)

(** Now suppose we have:

       f : Person -> C
       g : (Student->C) -> D

    Is it safe to allow the application [g f]?

    Again yes.

    So we want:

      Person -> C  <:  Student -> C

    I.e., arrow is _contravariant_ in its left-hand argument. *)

(** Putting these together...

                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2
*)

(* QUIZ

    Suppose we have  [S <: T] and [U <: V].  Which of the following
    subtyping assertions is _false_?

    (A) [S*U <: T*V]

    (B) [T->U <: S->U]

    (C) [(S->U) -> (S*V)  <:  (S->U) -> (T*U)]

    (D) [(T*U) -> V  <:  (S*U) -> V]

    (E) [S->U <: S->V]
*)

(* QUIZ

    Suppose again that we have [S <: T] and [U <: V].  Which of the
    following is incorrect?

    (A) [(T->T)*U  <: (S->T)*V]

    (B) [T->U <: S->V]

    (C) [(S->U) -> (S->V)  <:  (T->U) -> (T->V)]

    (D) [(S->V) -> V  <:  (T->U) -> V]

    (E) [S -> (V->U) <: S -> (U->U)]
*)

(* ----------------------------------------------------------------- *)
(** *** Records *)

(** What about subtyping for record types? *)

(** The basic intuition is that it is always safe to use a "bigger"
    record in place of a "smaller" one.  That is, given a record type,
    adding extra fields will always result in a subtype.  If some code
    is expecting a record with fields [x] and [y], it is perfectly safe
    for it to receive a record with fields [x], [y], and [z]; the [z]
    field will simply be ignored.  For example,

    {name:String, age:Nat, gpa:Nat} <: {name:String, age:Nat}
    {name:String, age:Nat} <: {name:String}
    {name:String} <: {}

    This is known as "width subtyping" for records. *)

(** We can also create a subtype of a record type by replacing the type
    of one of its fields with a subtype.  If some code is expecting a
    record with a field [x] of type [T], it will be happy with a record
    having a field [x] of type [S] as long as [S] is a subtype of
    [T]. For example,

    {x:Student} <: {x:Person}

    This is known as "depth subtyping". *)

(** Finally, although the fields of a record type are written in a
    particular order, the order does not really matter. For example,

    {name:String,age:Nat} <: {age:Nat,name:String}

    This is known as "permutation subtyping". *)

(** We _could_ formalize these requirements in a single subtyping rule
    for records as follows:

                        forall jk in j1..jn,
                    exists ip in i1..im, such that
                          jk=ip and Sp <: Tk
                  ----------------------------------                    (S_Rcd)
                  {i1:S1...im:Sm} <: {j1:T1...jn:Tn}

    That is, the record on the left should have all the field labels of
    the one on the right (and possibly more), while the types of the
    common fields should be in the subtype relation.

    However, this rule is rather heavy and hard to read, so it is often
    decomposed into three simpler rules, which can be combined using
    [S_Trans] to achieve all the same effects. *)

(** First, adding fields to the end of a record type gives a subtype:

                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm}

    We can use [S_RcdWidth] to drop later fields of a multi-field
    record while keeping earlier fields, showing for example that
    [{age:Nat,name:String} <: {age:Nat}]. *)

(** Second, subtyping can be applied inside the components of a compound
    record type:

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}

    For example, we can use [S_RcdDepth] and [S_RcdWidth] together to
    show that [{y:Student, x:Nat} <: {y:Person}]. *)

(** Third, subtyping can reorder fields.  For example, we
    want [{name:String, gpa:Nat, age:Nat} <: Person], but we
    haven't quite achieved this yet: using just [S_RcdDepth] and
    [S_RcdWidth] we can only drop fields from the _end_ of a record
    type.  So we add:

         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn}
*)

(** It is worth noting that full-blown language designs may choose not
    to adopt all of these subtyping rules. For example, in Java:

    - Each class member (field or method) can be assigned a single
      index, adding new indices "on the right" as more members are
      added in subclasses (i.e., no permutation for classes).

    - A class may implement multiple interfaces -- so-called "multiple
      inheritance" of interfaces (i.e., permutation is allowed for
      interfaces).

    - In early versions of Java, a subclass could not change the
      argument or result types of a method of its superclass (i.e., no
      depth subtyping or no arrow subtyping, depending how you look at
      it). *)

(* ----------------------------------------------------------------- *)
(** *** Top *)

(** Finally, it is convenient to give the subtype relation a maximum
    element -- a type that lies above every other type and is
    inhabited by all (well-typed) values.  We do this by adding to the
    language one new type constant, called [Top], together with a
    subtyping rule that places it above every other type in the
    subtype relation:

                                   --------                             (S_Top)
                                   S <: Top

    The [Top] type is an analog of the [Object] type in Java and C#. *)

(* ----------------------------------------------------------------- *)
(** *** Summary *)

(** In summary, we form the STLC with subtyping by starting with the
    pure STLC (over some set of base types) and then...

    - adding a base type [Top],

    - adding the rule of subsumption

                         Gamma |-- t1 \in T1     T1 <: T2
                         --------------------------------            (T_Sub)
                               Gamma |-- t1 \in T2

      to the typing relation, and

    - defining a subtype relation as follows:

                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T

                                   ------                              (S_Refl)
                                   T <: T

                                   --------                             (S_Top)
                                   S <: Top

                            S1 <: T1    S2 <: T2
                            --------------------                       (S_Prod)
                             S1 * S2 <: T1 * T2

                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2

                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm}

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}

         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn}
*)

(* QUIZ

    Suppose we have  [S <: T] and [U <: V].  Which of the following
    subtyping assertions is false?

    (A) [S*U <: Top]

    (B) [{i1:S,i2:T}->U <: {i1:S,i2:T,i3:V}->U]

    (C) [(S->T) -> (Top -> Top)  <:  (S->T) -> Top]

    (D) [(Top -> Top) -> V  <:  Top -> V]

    (E) [S -> {i1:U,i2:V} <: S -> {i2:V,i1:U}]
*)

(* QUIZ

    How about these?

    (A) [ {i1:Top} <: Top]

    (B) [Top -> (Top -> Top)  <:  Top -> Top]

    (C) [{i1:T} -> {i1:T}  <:  {i1:T,i2:S} -> Top]

    (D) [{i1:T,i2:V,i3:V} <: {i1:S,i2:U} * {i3:V}]

    (E) [Top -> {i1:U,i2:V} <: {i1:S} -> {i2:V,i1:V}]
*)

(* QUIZ
   What is the _smallest_ type [T] that makes the following
   assertion true?

       a:A |-- (\p:(A*T), (p.snd) (p.fst)) (a, \z:A,z) \in A

   (A) [Top]

   (B) [A]

   (C) [Top->Top]

   (D) [Top->A]

   (E) [A->A]

   (6) [A->Top]
*)

(* QUIZ
   What is the _largest_ type [T] that makes the following
   assertion true?

       a:A |-- (\p:(A*T), (p.snd) (p.fst)) (a, \z:A,z) \in A

   (A) [Top]

   (B) [A]

   (C) [Top->Top]

   (D) [Top->A]

   (E) [A->A]

   (6) [A->Top]
*)

(* QUIZ
   "The type [Bool] has no proper subtypes."  (I.e., the only
   type smaller than [Bool] is [Bool] itself.)

   (A) True

   (B) False
*)

(* QUIZ
   "Suppose [S], [T1], and [T2] are types with [S <: T1 -> T2].  Then
   [S] itself is an arrow type -- i.e., [S = S1 -> S2] for some [S1]
   and [S2] -- with [T1] <: [S1] and [S2 <: T2]."

   (A) True

   (B) False
*)

(* ################################################################# *)
(** * Formal Definitions *)

Module STLCSub.

(** Most of the definitions needed to formalize what we've discussed
    above -- in particular, the syntax and operational semantics of
    the language -- are identical to what we saw in the last chapter.
    We just need to extend the typing relation with the subsumption
    rule and add a new [Inductive] definition for the subtyping
    relation.  Let's first do the identical bits. *)

(* ----------------------------------------------------------------- *)
(** *** Syntax *)

(** (Omitting records, to avoid dealing with "[...]" stuff.) *)

Inductive ty : Type :=
  | Ty_Top   : ty
  | Ty_Bool  : ty
  | Ty_Base  : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Unit  : ty
.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_unit : tm
.

(** Standard [Custom Entry] nonsense... *)
Declare Custom Entry stlc_ty.
Declare Custom Entry stlc_tm.
Declare Scope stlc_scope.
Open Scope stlc_scope.

Notation "x" := x (in custom stlc_ty at level 0, x global) : stlc_scope.

Notation "<{{ x }}>" := x (x custom stlc_ty).

Notation "( t )" := t (in custom stlc_ty at level 0, t custom stlc_ty) : stlc_scope.
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc_ty at level 99, right associativity) : stlc_scope.

Notation "$( t )" := t (in custom stlc_ty at level 0, t constr) : stlc_scope.

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

Notation "'Base' x" := (Ty_Base x) (in custom stlc_ty at level 0, x constr at level 0) : stlc_scope.

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc_ty at level 0) : stlc_scope.
Notation "'unit'" := tm_unit (in custom stlc_tm at level 0) : stlc_scope.

Notation "'Top'" := (Ty_Top) (in custom stlc_ty at level 0) : stlc_scope.

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

(** The definition of substitution remains exactly the same as for the
    pure STLC. *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc_tm at level 5, x global, s custom stlc_tm,
      t custom stlc_tm at next level, right associativity).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{unit}> =>
      <{unit}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc_tm) : stlc_scope.

(* ----------------------------------------------------------------- *)
(** *** Reduction *)

(** Likewise the definitions of [value] and [step]. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_unit :
      value <{unit}>
.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
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

(* ================================================================= *)
(** ** Subtyping *)

(** The definition of subtyping is just what we sketched in the
    motivating discussion. *)

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: <{{ Top }}>
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      <{{ S1->S2 }}> <: <{{ T1->T2 }}>
where "T '<:' U" := (subtype T U).

(** Note that we don't need any special rules for base types ([Bool]
    and [Base]): they are automatically subtypes of themselves (by
    [S_Refl]) and [Top] (by [S_Top]), and that's all we want. *)

Hint Constructors subtype : core.

(* ================================================================= *)
(** ** Typing *)

(** The only change to the typing relation is the addition of the rule
    of subsumption, [T_Sub]. *)

Definition context := partial_map ty.

Notation "x '|->' v ';' m " := (update m x v)
  (in custom stlc_tm at level 0, x constr at level 0, v  custom stlc_ty, right associativity) : stlc_scope.

Notation "x '|->' v " := (update empty x v)
  (in custom stlc_tm at level 0, x constr at level 0, v custom stlc_ty) : stlc_scope.

Notation "'empty'" := empty (in custom stlc_tm) : stlc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
            (at level 0, Gamma custom stlc_tm at level 200, t custom stlc_tm, T custom stlc_ty).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Pure STLC, same as before: *)
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
  | T_Unit : forall Gamma,
      <{ Gamma |-- unit \in Unit }>
  (* New rule of subsumption: *)
  | T_Sub : forall Gamma t1 T1 T2,
      <{ Gamma |-- t1 \in T1 }> ->
      T1 <: T2 ->
      <{ Gamma |-- t1 \in T2 }>

where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T) : stlc_scope.

Hint Constructors has_type : core.

(* ################################################################# *)
(** * Properties *)

(** We want the same properties as always: progress + preservation.

      - _Statements_ of these theorems don't need to change, compared
        to pure STLC

      - But _proofs_ are a bit more involved, to account for the
        additional flexibility in the typing relation *)

(* ================================================================= *)
(** ** Inversion Lemmas for Subtyping *)

(** Before we look at the properties of the typing relation, we need
    to establish a couple of critical structural properties of the
    subtype relation:
       - [Bool] is the only subtype of [Bool], and
       - every subtype of an arrow type is itself an arrow type. *)

(** Formally: *)

Lemma sub_inversion_Bool : forall U,
     U <: <{{ Bool }}> ->
     U = <{{ Bool }}>.
Proof with auto.
  intros U Hs.
  remember <{{ Bool }}> as V.
  (* FILL IN HERE *) Admitted.

Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{{ V1->V2 }}> ->
     exists U1 U2,
     U = <{{ U1->U2 }}> /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{{ V1->V2 }}> as V.
  generalize dependent V2. generalize dependent V1.
  (* FILL IN HERE *) Admitted.


(* ================================================================= *)
(** ** Canonical Forms *)

(** The proof of progress uses facts of the form "every value
    belonging to an arrow type is an abstraction."

    In the pure STLC, such facts are "immediate from the
    definition" (formally, they follow directly by [inversion]).

    With subtyping, they require real proofs by induction... *)

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  <{ Gamma |-- s \in T1->T2 }> ->
  value s ->
  exists x S1 s2,
     s = <{\x:S1,s2}>.
Proof with eauto.
  (* FILL IN HERE *) Admitted.

(** Similarly, the canonical forms of type [Bool] are the constants
    [tm_true] and [tm_false]. *)

Lemma canonical_forms_of_Bool : forall Gamma s,
  <{ Gamma |-- s \in Bool }> ->
  value s ->
  s = tm_true \/ s = tm_false.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember <{{ Bool }}> as T.
  induction Hty; try solve_by_invert...
  - (* T_Sub *)
    subst. apply sub_inversion_Bool in H. subst...
Qed.

(* ================================================================= *)
(** ** Progress *)

(** _Theorem_ (Progress): For any term [t] and type [T], if [empty |--
    t \in T] then [t] is a value or [t --> t'] for some term [t'].

    _Proof_: Let [t] and [T] be given, with [empty |-- t \in T].
    Proceed by induction on the typing derivation.

    The cases for [T_Abs], [T_Unit], [T_True] and [T_False] are
    immediate because abstractions, [unit], [true], and
    [false] are already values.  The [T_Var] case is vacuous
    because variables cannot be typed in the empty context.  The
    remaining cases are more interesting:

    - If the last step in the typing derivation uses rule [T_App],
      then there are terms [t1] [t2] and types [T1] and [T2] such that
      [t = t1 t2], [T = T2], [empty |-- t1 \in T1 -> T2], and [empty
      |-- t2 \in T1].  Moreover, by the induction hypothesis, either
      [t1] is a value or it steps, and either [t2] is a value or it
      steps.  There are three possibilities to consider:

      - First, suppose [t1 --> t1'] for some term [t1'].  Then [t1
        t2 --> t1' t2] by [ST_App1].

      - Second, suppose [t1] is a value and [t2 --> t2'] for some term
        [t2'].  Then [t1 t2 --> t1 t2'] by rule [ST_App2] because [t1]
        is a value.

      - Third, suppose [t1] and [t2] are both values.  By the
        canonical forms lemma for arrow types, we know that [t1] has
        the form [\x:S1,s2] for some [x], [S1], and [s2].  But then
        [(\x:S1,s2) t2 --> [x:=t2]s2] by [ST_AppAbs], since [t2] is a
        value.

    - If the final step of the derivation uses rule [T_If], then
      there are terms [t1], [t2], and [t3] such that [t = if t1
      then t2 else t3], with [empty |-- t1 \in Bool] and with [empty
      |-- t2 \in T] and [empty |-- t3 \in T].  Moreover, by the
      induction hypothesis, either [t1] is a value or it steps.

       - If [t1] is a value, then by the canonical forms lemma for
         booleans, either [t1 = true] or [t1 = false].  In
         either case, [t] can step, using rule [ST_IfTrue] or
         [ST_IfFalse].

       - If [t1] can step, then so can [t], by rule [ST_If].

    - If the final step of the derivation is by [T_Sub], then there is
      a type [T2] such that [T1 <: T2] and [empty |-- t1 \in T1].  The
      desired result is exactly the induction hypothesis for the
      typing subderivation. *)

(** Formally: *)

Theorem progress : forall t T,
     <{ empty |-- t \in T }> ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.
  - (* T_Var *)
    discriminate.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        eapply canonical_forms_of_arrow_types in Ht1; [|assumption].
        destruct Ht1 as [x [S1 [s2 H1]]]. subst.
        exists (<{ [x:=t2]s2 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_If *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + apply canonical_forms_of_Bool in Ht1; [|assumption].
      destruct Ht1; subst...
    + destruct H. rename x into t1'. eauto.
Qed.

(* ================================================================= *)
(** ** Inversion Lemmas for Typing *)

(** We also need to prove an inversion lemma corresponding to a
    structural fact about the typing relation that is "obvious from
    the definition" in pure STLC. *)

(** _Lemma_: If [Gamma |-- \x:S1,t2 \in T], then there is a type [S2]
    such that [x|->S1; Gamma |-- t2 \in S2] and [S1 -> S2 <: T].

    Notice that the lemma does _not_ say, "then [T] itself is an arrow
    type" -- this is tempting, but false!  (Why?) *)

(** _Lemma_: If [Gamma |-- \x:S1,t2 \in T], then there is a type [S2]
    such that [x|->S1; Gamma |-- t2 \in S2] and [S1 -> S2 <: T]. *)

(** _Proof_: Let [Gamma], [x], [S1], [t2] and [T] be given as
     described.  Proceed by induction on the derivation of [Gamma |--
     \x:S1,t2 \in T].  The cases for [T_Var] and [T_App] are vacuous
     as those rules cannot be used to give a type to a syntactic
     abstraction.

     - If the last step of the derivation is a use of [T_Abs] then
       there is a type [T12] such that [T = S1 -> T12] and [x:S1;
       Gamma |-- t2 \in T12].  Picking [T12] for [S2] gives us what we
       need, since [S1 -> T12 <: S1 -> T12] follows from [S_Refl].

     - If the last step of the derivation is a use of [T_Sub] then
       there is a type [S] such that [S <: T] and [Gamma |-- \x:S1,t2
       \in S].  The IH for the typing subderivation tells us that there
       is some type [S2] with [S1 -> S2 <: S] and [x:S1; Gamma |-- t2
       \in S2].  Picking type [S2] gives us what we need, since [S1 ->
       S2 <: T] then follows by [S_Trans]. *)

(** Formally: *)

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     <{ Gamma |-- \x:S1,t2 \in T }> ->
     exists S2,
       <{{ S1->S2 }}> <: T
       /\ <{ x |-> S1 ; Gamma |-- t2 \in S2 }>.
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember <{\x:S1,t2}> as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    exists T1...
  - (* T_Sub *)
    destruct IHhas_type as [S2 [Hsub Hty]]...
  Qed.

(** Similarly: *)
Lemma typing_inversion_var : forall Gamma (x:string) T,
  <{ Gamma |-- x \in T }> ->
  exists S,
    Gamma x = Some S /\ S <: T.
Proof with eauto.
  (* FILL IN HERE *) Admitted.

Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  <{ Gamma |-- t1 t2 \in T2 }> ->
  exists T1,
    <{ Gamma |-- t1 \in T1->T2 }> /\
    <{ Gamma |-- t2 \in T1 }>.
Proof with eauto.
  (* FILL IN HERE *) Admitted.

Lemma typing_inversion_unit : forall Gamma T,
  <{ Gamma |-- unit \in T }> ->
  <{{ Unit }}> <: T.
Proof with eauto.
  intros Gamma T Htyp. remember <{ unit }> as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

(** The inversion lemmas for typing and for subtyping between arrow
    types can be packaged up as a useful "combination lemma" telling
    us exactly what we'll actually require below. *)

Lemma abs_arrow : forall x S1 s2 T1 T2,
  <{ empty |-- \x:S1,s2 \in T1->T2 }> ->
  T1 <: S1
  /\ <{ x |-> S1 |-- s2 \in T2 }>.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  injection Heq as Heq; subst...  Qed.

(* ================================================================= *)
(** ** Weakening *)

(** The weakening lemma is proved as in pure STLC. *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     <{ Gamma  |-- t \in T }> ->
     <{ Gamma' |-- t \in T }>.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Corollary weakening_empty : forall Gamma t T,
     <{ empty |-- t \in T }> ->
     <{ Gamma |-- t \in T }>.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* ================================================================= *)
(** ** Substitution *)

(** The _substitution lemma_ is stated exactly as in pure STLC.

    The proof is also the same except that here it is easier to use
    induction on typing derivations rather than on terms. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
   <{ x |-> U ; Gamma |-- t \in T }> ->
   <{ empty |-- v \in U }>  ->
   <{ Gamma |-- [x:=v]t \in T }>.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
 (* FILL IN HERE *) Admitted.

(* ================================================================= *)
(** ** Preservation *)

(** The proof of preservation now proceeds pretty much as in earlier
    chapters, using the substitution lemma at the appropriate point
    and the inversion lemma from above to extract structural
    information from typing assumptions. *)

(** _Theorem_ (Preservation): If [t], [t'] are terms and [T] is a type
    such that [empty |-- t \in T] and [t --> t'], then [empty |-- t'
    \in T].

    _Proof_: Let [t] and [T] be given such that [empty |-- t \in T].
    We proceed by induction on the structure of this typing
    derivation. The [T_Abs], [T_Unit], [T_True], and [T_False] cases
    are vacuous because abstractions and constants don't step.  Case
    [T_Var] is vacuous as well, since the context is empty.

     - If the final step of the derivation is by [T_App], then there
       are terms [t1] and [t2] and types [T1] and [T2] such that [t =
       t1 t2], [T = T2], [empty |-- t1 \in T1 -> T2], and [empty |--
       t2 \in T1].

       By the definition of the step relation, there are three ways
       [t1 t2] can step.  Cases [ST_App1] and [ST_App2] follow
       immediately by the induction hypotheses for the typing
       subderivations and a use of [T_App].

       Suppose instead [t1 t2] steps by [ST_AppAbs].  Then [t1 =
       \x:S,t12] for some type [S] and term [t12], and [t' =
       [x:=t2]t12].

       By lemma [abs_arrow], we have [T1 <: S] and [x:S1 |-- s2 \in
       T2].  It then follows by the substitution
       lemma ([substitution_preserves_typing]) that [empty |-- [x:=t2]
       t12 \in T2] as desired.

     - If the final step of the derivation uses rule [T_If], then
       there are terms [t1], [t2], and [t3] such that [t = if t1 then
       t2 else t3], with [empty |-- t1 \in Bool] and with [empty |--
       t2 \in T] and [empty |-- t3 \in T].  Moreover, by the induction
       hypothesis, if [t1] steps to [t1'] then [empty |-- t1' : Bool].
       There are three cases to consider, depending on which rule was
       used to show [t --> t'].

          - If [t --> t'] by rule [ST_If], then [t' = if t1' then t2
            else t3] with [t1 --> t1'].  By the induction hypothesis,
            [empty |-- t1' \in Bool], and so [empty |-- t' \in T] by
            [T_If].

          - If [t --> t'] by rule [ST_IfTrue] or [ST_IfFalse], then
            either [t' = t2] or [t' = t3], and [empty |-- t' \in T]
            follows by assumption.

     - If the final step of the derivation is by [T_Sub], then there
       is a type [S] such that [S <: T] and [empty |-- t \in S].  The
       result is immediate by the induction hypothesis for the typing
       subderivation and an application of [T_Sub].  [] *)

Theorem preservation : forall t t' T,
     <{ empty |-- t \in T }> ->
     t --> t'  ->
     <{ empty |-- t' \in T }>.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; eauto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T0...
Qed.


End STLCSub.


(** * ProofObjects: The Curry-Howard Correspondence *)

Set Warnings "-notation-overridden,-notation-incompatible-prefix".
From LF Require Export IndProp.

(** "Algorithms are the computational content of proofs."
    (Robert Harper) *)

(** Programming and proving in Rocq are two sides of the same coin.
    Proofs manipulate evidence much as programs manipulate data. *)

(** Question: If evidence is data, what are propositions themselves?

    Answer: They are types! *)

(** Look again at the formal definition of the [ev] property.  *)

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** We can pronounce the ":" here as either "has type" or "is a proof
    of."  For example, the second line in the definition of [ev]
    declares that [ev_0 : ev 0].  Instead of "[ev_0] has type [ev 0],"
    we can say that "[ev_0] is a proof of [ev 0]." *)

(** This pun between types and propositions -- between [:] as "has type"
    and [:] as "is a proof of" or "is evidence for" -- is called the
    _Curry-Howard correspondence_.  It proposes a deep connection
    between the world of logic and the world of computation:

                 propositions  ~  types
                 proofs        ~  programs

    See [Wadler 2015] (in Bib.v) for a brief history and modern exposition. *)

(** Many useful insights follow from this connection.  To begin with,
    it gives us a natural interpretation of the type of the [ev_SS]
    constructor: *)

Check ev_SS
  : forall n,
      ev n ->
      ev (S (S n)).

(** This can be read "[ev_SS] is a constructor that takes two
    arguments -- a number [n] and evidence for the proposition [ev
    n] -- and yields evidence for the proposition [ev (S (S n))]." *)

(** Now let's look again at an earlier proof involving [ev]. *)

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** Just as with ordinary data values and functions, we can use the
    [Print] command to see the _proof object_ that results from this
    proof script. *)

Print ev_4.
(* ===> ev_4 = ev_SS 2 (ev_SS 0 ev_0)
      : ev 4  *)

(** Indeed, we can also write down this proof object directly,
    with no need for a proof script at all: *)

Check (ev_SS 2 (ev_SS 0 ev_0))
  : ev 4.

(** Similarly, as we've seen, we can directly apply theorems to
    arguments in proof scripts: *)

Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

(* ################################################################# *)
(** * Proof Scripts *)

(** When we write a proof using tactics, what we are doing is
    instructing Rocq to build a proof object under the hood.  We can
    see this using [Show Proof]: *)

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

(** Tactic proofs are convenient, but they are not essential in Rocq:
    in principle, we can always just construct the required evidence
    by hand. Then we can use [Definition] (rather than [Theorem]) to
    introduce a global name for this evidence. *)

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

(* ################################################################# *)
(** * Quantifiers, Implications, Functions *)

(** In Rocq's computational universe (where data structures and
    programs live), there are two sorts of values that have arrows in
    their types: _constructors_ introduced by [Inductive]ly defined
    data types, and _functions_.

    Similarly, in Rocq's logical universe (where we carry out proofs),
    there are two ways of giving evidence for an implication:
    constructors introduced by [Inductive]ly defined propositions,
    and... functions! *)

(** For example, consider this statement: *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

(** What is the proof object corresponding to [ev_plus4]? *)

(** We're looking for an expression whose _type_ is [forall n, ev n ->
    ev (4 + n)] -- that is, a _function_ that takes two arguments (one
    number and a piece of evidence) and returns a piece of evidence!

    Here it is: *)

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

(** Or equivalently: *)

Definition ev_plus4'' (n : nat) (H : ev n)
                    : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4'' : forall n : nat, ev n -> ev (4 + n).

(** When we view the proposition being proved by [ev_plus4] as a
    function type, one interesting point becomes apparent: The second
    argument's type, [ev n], mentions the _value_ of the first
    argument, [n].

    While such _dependent types_ are not found in most mainstream
    programming languages, they can be quite useful in programming
    too, as the flurry of activity in the functional programming
    community over the past couple of decades demonstrates. *)

(** Notice that both implication ([->]) and quantification ([forall])
    correspond to functions on evidence.  In fact, they are really the
    same thing: [->] is just a shorthand for a degenerate use of
    [forall] where there is no dependency, i.e., no need to give a
    name to the type on the left-hand side of the arrow:

           forall (x:nat), nat
        =  forall (_:nat), nat
        =  nat          -> nat
*)

(* QUIZ

    Recall the definition of [ev]:

       Inductive ev : nat -> Prop :=
         | ev_0 : ev 0
         | ev_SS : forall n, ev n -> ev (S (S n)).

    What is the type of this expression?

       fun (n : nat) =>
         fun (H : ev n) =>
            ev_SS (2 + n) (ev_SS n H)

  (A) [forall n, ev n]

  (B) [forall n, ev (2 + n)]

  (C) [forall n, ev n -> ev n]

  (D) [forall n, ev n -> ev (2 + n)]

  (E) [forall n, ev n -> ev (4 + n)]

  (F) Not typeable
*)







Check (fun (n : nat) =>
         fun (H : ev n) =>
            ev_SS (2 + n) (ev_SS n H))
       : forall n : nat, ev n -> ev (4 + n).

(* ################################################################# *)
(** * Programming with Tactics *)

(** If we can build proofs by giving explicit terms rather than
    executing tactic scripts, you may wonder whether we can build
    _programs_ using tactics rather than by writing down explicit
    terms.

    Naturally, the answer is yes! *)

Definition add2 : nat -> nat.
intros n.
Show Proof.
apply S.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add2.
(* ==>
    add2 = fun n : nat => S (S n)
          : nat -> nat
*)

Compute add2 2.
(* ==> 4 : nat *)

(* ################################################################# *)
(** * Logical Connectives as Inductive Types *)

(** Inductive definitions are powerful enough to express most of the
    logical connectives we have seen so far.  Indeed, only universal
    quantification (with implication as a special case) is built into
    Rocq; all the others are defined inductively.

    Let's see how. *)

Module Props.

(* ================================================================= *)
(** ** Conjunction *)

(** To prove that [P /\ Q] holds, we must present evidence for both
    [P] and [Q].  Thus, it makes sense to define a proof object for
    [P /\ Q] to consist of a pair of two proofs: one for [P] and
    another one for [Q]. This leads to the following definition. *)

Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

(** Notice the similarity with the definition of the [prod] type,
    given in chapter [Poly]; the only difference is that [prod] takes
    [Type] arguments, whereas [and] takes [Prop] arguments. *)

Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)

(** This similarity should clarify why [destruct] and [intros]
    patterns can be used on a conjunctive hypothesis.  Case analysis
    allows us to consider all possible ways in which [P /\ Q] was
    proved -- here just one (the [conj] constructor). *)

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.

(** Similarly, the [split] tactic actually works for any inductively
    defined proposition with exactly one constructor.  In particular,
    it works for [and]: *)

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

End And.

(** This shows why the inductive definition of [and] can be
    manipulated by tactics as we've been doing.  We can also use it to
    build proofs directly, using pattern-matching.  For instance: *)

Definition proj1'' P Q (HPQ : P /\ Q) : P :=
  match HPQ with
  | conj HP HQ => HP
  end.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(* QUIZ

    What is the type of this expression?

        fun P Q R (H1: and P Q) (H2: and Q R) =>
          match (H1,H2) with
          | (conj HP _, conj  _ HR) => conj HP HR
          end.

  (A) [forall P Q R, P /\ Q -> Q /\ R -> P /\ R]

  (B) [forall P Q R, Q /\ P -> R /\ Q -> P /\ R]

  (C) [forall P Q R, P /\ R]

  (D) [forall P Q R, P \/ Q -> Q \/ R -> P \/ R]

  (E) Not typeable

*)
Check
  (fun P Q R (H1: and P Q) (H2: and Q R) =>
    match (H1,H2) with
    | (conj HP _, conj _ HR) => conj HP HR
    end) : forall P Q R, P /\ Q -> Q /\ R -> P /\ R.

(* ================================================================= *)
(** ** Disjunction *)

(** The inductive definition of disjunction uses two constructors, one
    for each side of the disjunction: *)

Module Or.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q) : type_scope.

(** This declaration explains the behavior of the [destruct] tactic on
    a disjunctive hypothesis, since the generated subgoals match the
    shape of the [or_introl] and [or_intror] constructors. *)

(** Once again, we can also directly write proof objects for theorems
    involving [or], without resorting to tactics. *)

Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.

Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Proof.
  intros P Q HP. left. apply HP.
  Show Proof.
Qed.

Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
Qed.

End Or.

(* QUIZ

    What is the type of this expression?

       fun P Q H =>
         match H with
         | or_introl HP => @or_intror Q P HP
         | or_intror HQ => @or_introl Q P HQ
         end.

  (A) [forall P Q H, Q \/ P \/ H]

  (B) [forall P Q, P \/ Q -> P \/ Q]

  (C) [forall P Q H, P \/ Q -> Q \/ P -> H]

  (D) [forall P Q, P \/ Q -> Q \/ P]

  (E) Not typeable

*)
Check (fun P Q H =>
      match H with
      | or_introl HP => @or_intror Q P HP
      | or_intror HQ => @or_introl Q P HQ
      end) : forall P Q, P \/ Q -> Q \/ P.

(* ================================================================= *)
(** ** Existential Quantification *)

(** To give evidence for an existential quantifier, we package a
    witness [x] together with a proof that [x] satisfies the property
    [P]: *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.

End Ex.

(** The more familiar form [exists x, ev x] desugars to an expression
    involving [ex]: *)

Check ex (fun n => ev n) : Prop.

(** Here's how to define an explicit proof object involving [ex]: *)

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(* QUIZ

    Which of the following propositions is proved by
    providing an explicit witness [w] using [exist w]?

    (A) [forall x: nat, (exists n, x = S n) -> (x<>0)]

    (B) [forall x: nat, (x<>0) -> (exists n, x = S n)]

    (C) [forall x: nat, (x=0) ->  ~(exists n, x = S n)]

    (D) [forall x: nat, x = 4 -> (x<>0)]

    (E) none of the above

*)



Goal forall x: nat, (x<>0) -> (exists n, x = S n).
Proof.
intros. destruct x as [| x'].
- exfalso. apply H. reflexivity.
- exists x'. reflexivity.
Qed.

(** To destruct existentials in a proof term we simply use match: *)
Definition dist_exists_or_term (X:Type) (P Q : X -> Prop) :
  (exists x, P x \/ Q x) -> (exists x, P x) \/ (exists x, Q x) :=
  fun H => match H with
           | ex_intro _ x Hx =>
               match Hx with
               | or_introl HPx => or_introl (ex_intro _ x HPx)
               | or_intror HQx => or_intror (ex_intro _ x HQx)
               end
           end.

(* ================================================================= *)
(** ** [True] and [False] *)

(** The inductive definition of the [True] proposition is simple: *)

Inductive True : Prop :=
  | I : True.

(** It has one constructor (so every proof of [True] is the same, so
    being given a proof of [True] is not informative.) *)

(** [False] is equally simple -- indeed, so simple it may look
    syntactically wrong at first glance! *)

Inductive False : Prop := .

(** That is, [False] is an inductive type with _no_ constructors --
    i.e., no way to build evidence for it. For example, there is
    no way to complete the following definition such that it
    succeeds. *)

Fail
  Definition contra : False :=
  42.

(** But it is possible to destruct [False] by pattern matching. There can
    be no patterns that match it, since it has no constructors.  So
    the pattern match also is so simple it may look syntactically
    wrong at first glance. *)

Definition false_implies_zero_eq_one : False -> 0 = 1 :=
  fun contra => match contra with end.

(** Since there are no branches to evaluate, the [match] expression
    can be considered to have any type we want, including [0 = 1].
    Fortunately, it's impossible to ever cause the [match] to be
    evaluated, because we can never construct a value of type [False]
    to pass to the function. *)

End Props.

(* ################################################################# *)
(** * Equality *)

(** Even Rocq's equality relation is not built in.  We can define
    it ourselves: *)

Module EqualityPlayground.

Inductive eq {X:Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                       (at level 70, no associativity)
                     : type_scope.

(** Rocq terms are "the same" if they are _convertible_
    according to a simple set of computation rules: evaluation of
    function applications, inlining of definitions, and simplification
    of [match]es. *)

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

(** [reflexivity] is essentially just [apply eq_refl]. *)

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[]  :=
  fun (X:Type) (x:X) => eq_refl [x].

(** We can also pattern-match on an equality proof: *)
Definition eq_add : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2) :=
  fun n1 n2 Heq =>
    match Heq with
    | eq_refl n => eq_refl (S n)
    end.

(** A tactic-based proof runs into some difficulties if we try to use
    our usual repertoire of tactics, such as [rewrite] and
    [reflexivity]. Those work with *setoid* relations that Rocq knows
    about, such as [=], but not our [==]. We could prove to Rocq that
    [==] is a setoid, but a simpler way is to use [destruct] and
    [apply] instead. *)

Theorem eq_add' : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2).
Proof.
  intros n1 n2 Heq.
  Fail rewrite Heq. (* doesn't work for _our_ == relation *)
  destruct Heq as [n]. (* n1 and n2 replaced by n in the goal! *)
  Fail reflexivity. (* doesn't work for _our_ == relation *)
  apply eq_refl.
Qed.

(* QUIZ

    Which of the following is a correct proof object for the proposition

    exists x, x + 3 == 4

?

    (A) [eq_refl 4]

    (B) [ex_intro (z + 3 == 4) 1 (eq_refl 4)]

    (C) [ex_intro (fun z => (z + 3 == 4)) 1 (eq_refl 4)]

    (D) [ex_intro (fun z => (z + 3 == 4)) 1 (eq_refl 1)]

    (E) none of the above
*)




Fail Definition quiz1 : exists x, x + 3 == 4
  := eq_refl 4.
Fail Definition quiz2 : exists x, x + 3 == 4
  := ex_intro (z + 3 == 4) 1 (eq_refl 4).
Definition quiz3 : exists x, x + 3 == 4
  := ex_intro (fun z => (z + 3 == 4)) 1 (eq_refl 4).
Fail Definition quiz4 : exists x, x + 3 == 4
  := ex_intro (fun z => (z + 3 == 4)) 1 (eq_refl 1).

End EqualityPlayground.

(* ################################################################# *)
(** * Rocq's Trusted Computing Base *)

(** The Coq typechecker is what actually checks our proofs.  We
    have to trust it, but it's relatively small and
    straightforward. *)

(** For example, it rejects this broken proof: *)

Fail Definition or_bogus : forall P Q, P \/ Q -> P :=
  fun (P Q : Prop) (A : P \/ Q) =>
    match A with
    | or_introl H => H
    end.

(** And these: *)

Fail Fixpoint infinite_loop {X : Type} (n : nat) {struct n} : X :=
  infinite_loop n.

Fail Definition falso : False := infinite_loop 0.

(** The tactic language and its implementation are _not_ part
    of Rocq's TCB.  This is fortunate, because complex tactics can (and
    occasionally do) produce invalid proof objects.  The [Qed] command
    runs the type checker to make sure that the proof object
    constructed by the tactic script is valid. *)


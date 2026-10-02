(** * Hoare2: Hoare Logic, Part II *)

Set Warnings "-notation-overridden".
Ltac intuition_solver ::= auto.
From Stdlib Require Import Strings.String.
From PLF Require Import Maps.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Import PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From PLF Require Export Imp.
From PLF Require Import Hoare.

Definition FILL_IN_HERE := <{True}>.

(* QUIZ

    On a piece of paper (or whatever), write down a Hoare-triple
    specification for the following program:

    X := 2;
    Y := X + X
*)

(* QUIZ

    Write down a (useful) specification for the following program:

    X := X + 1; Y := X + 1
*)

(* QUIZ

    Write down a (useful) specification for the following program:

    if X <= Y then
      skip
    else
      Z := X;
      X := Y;
      Y := Z
    end
*)

(* QUIZ

    Write down a (useful) specification for the following program:

    X := m;
    Y := X + X
*)

(* QUIZ

    Write down a (useful) specification for the following program:

    X := m;
    Z := 0;
    while X <> 0 do
      X := X - 2;
      Z := Z + 1
    end
*)

(* ################################################################# *)
(** * Decorated Programs *)

(** The beauty of Hoare Logic is that it is _syntax directed: the
    structure of proofs exactly follows the structure of programs.

    We can record the essential ideas of a Hoare-logic proof --
    omitting low-level calculational details -- by "decorating" a
    program with appropriate assertions on each of its commands.

    Such a _decorated program_ carries within itself an argument for
    its own correctness. *)

(** For example, consider the program:

    X := m;
    Z := p;
    while X <> 0 do
      Z := Z - 1;
      X := X - 1
    end
*)
(** Here is one possible specification for this program, in the
    form of a Hoare triple:

    {{ True }}
    X := m;
    Z := p;
    while X <> 0 do
      Z := Z - 1;
      X := X - 1
    end
    {{ Z = p - m }}
*)

(** Here is a decorated version of this program, embodying a
    proof of this specification:

    {{ True }} ->>
    {{ m = m }}
      X := m
                         {{ X = m }} ->>
                         {{ X = m /\ p = p }};
      Z := p;
                         {{ X = m /\ Z = p }} ->>
                         {{ Z - X = p - m }}
      while X <> 0 do
                         {{ Z - X = p - m /\ X <> 0 }} ->>
                         {{ (Z - 1) - (X - 1) = p - m }}
        Z := Z - 1
                         {{ Z - (X - 1) = p - m }};
        X := X - 1
                         {{ Z - X = p - m }}
      end
    {{ Z - X = p - m /\ ~ (X <> 0) }} ->>
    {{ Z = p - m }}
*)

(** Concretely, a decorated program consists of the program's text
    interleaved with assertions (sometimes multiple assertions
    separated by ->>). *)

(** A decorated program can be viewed as a compact representation of a
    proof in Hoare Logic: the assertions surrounding each command
    specify the Hoare triple to be proved for that part of the program
    using one of the Hoare Logic rules, and the structure of the
    program itself shows how to assemble all these individual steps
    into a proof for the whole program. *)

(* ================================================================= *)
(** ** Example: Swapping *)

(** Consider the following program, which swaps the values of two
    variables using addition and subtraction, instead of by assigning
    to a temporary variable.

       X := X + Y;
       Y := X - Y;
       X := X - Y

    We can give a proof, in the form of decorations, that this program is
    correct -- i.e., it really swaps [X] and [Y] -- as follows. *)
(* WORK IN CLASS *)

(* ================================================================= *)
(** ** Example: Simple Conditionals *)

(** Here's a simple program using conditionals, along
    with a possible specification:

     {{ True }}
       if X <= Y then
         Z := Y - X
       else
         Z := X - Y
       end
     {{ Z + X = Y \/ Z + Y = X }}

    Let's turn it into a decorated program...
*)
(* WORK IN CLASS *)

(* ================================================================= *)
(** ** Example: Reduce to Zero *)

(** Here is a very simple [while] loop with a simple
    specification:

        {{ True }}
          while (X <> 0) do
            X := X - 1
          end
        {{ X = 0 }}
*)
(* WORK IN CLASS *)

(* ================================================================= *)
(** ** Example: Division *)

(** Let's do one more example of simple reasoning about a loop.

    The following Imp program calculates the integer quotient and
    remainder of parameters [m] and [n].

       X := m;
       Y := 0;
       while n <= X do
         X := X - n;
         Y := Y + 1
       end;

    If we replace [m] and [n] by concrete numbers and execute the program, it
    will terminate with the variable [X] set to the remainder when [m]
    is divided by [n] and [Y] set to the quotient.

    Here's a possible specification:

      {{ True }}
        X := m;
        Y := 0;
        while n <= X do
          X := X - n;
          Y := Y + 1
        end
      {{ n * Y + X = m /\ X < n }}
*)
(* WORK IN CLASS *)

(* ================================================================= *)
(** ** From Decorated Programs to Formal Proofs *)

(** From an informal proof in the form of a decorated program, it is
    "easy in principle" to read off a formal proof using the Rocq
    theorems corresponding to the Hoare Logic rules, but these proofs
    can be a bit long and fiddly. *)

(** For example... *)
Definition reduce_to_zero : com :=
  <{ while X <> 0 do
       X := X - 1
     end }>.

Theorem reduce_to_zero_correct' :
  {{True}}
    reduce_to_zero
  {{X = 0}}.
Proof.
  unfold reduce_to_zero.
  (* First we need to transform the postcondition so
     that hoare_while will apply. *)
  eapply hoare_consequence_post.
  - apply hoare_while.
    + (* Loop body preserves loop invariant *)
      (* Massage precondition so [hoare_asgn] applies *)
      eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * (* Proving trivial implication (2) ->> (3) *)
        unfold assertion_sub, "->>". simpl. intros.
        exact I.
  - (* Loop invariant and negated guard imply post *)
    intros st [Inv GuardFalse].
    unfold bassertion in GuardFalse. simpl in GuardFalse.
    rewrite not_true_iff_false in GuardFalse.
    rewrite negb_false_iff in GuardFalse.
    apply eqb_eq in GuardFalse.
    apply GuardFalse.
Qed.

(** A little more (OK, quite a bit more) tactic fanciness for
    helping deal with the boring parts of the process of proving
    assertions: *)

Ltac verify_assertion :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold bassertion in *; unfold beval in *; unfold aeval in *;
  unfold assertion_sub; intros;
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq;
          [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] =>
                         destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  try eauto;
  try lia.

(** This makes it pretty easy to verify [reduce_to_zero]: *)

Theorem reduce_to_zero_correct''' :
  {{True}}
    reduce_to_zero
  {{X = 0}}.
Proof.
  unfold reduce_to_zero.
  eapply hoare_consequence_post.
  - apply hoare_while.
    + eapply hoare_consequence_pre.
      * apply hoare_asgn.
      * verify_assertion.
  - verify_assertion.
Qed.

(** This example shows that it is conceptually straightforward to read
    off the main elements of a formal proof from a decorated program.
    Indeed, the process is so straightforward that it can be
    automated, as we will see next. *)

(* ################################################################# *)
(** * Formal Decorated Programs *)

(** With a little more work, we can _formalize_ the definition of
    well-formed decorated programs and _automate_ the boring mechanical
    steps in proving that the decorations are correct. *)

(* ================================================================= *)
(** ** Syntax *)

(** The first thing we need to do is to formalize a variant of the
    syntax of Imp commands that includes embedded assertions, which
    we'll call "decorations."  We call the new commands _decorated
    commands_, or [dcom]s.

    The choice of exactly where to put assertions in the definition of
    [dcom] is a bit subtle.  The simplest thing to do would be to
    annotate every [dcom] with a precondition and postcondition --
    something like this... *)

Module DComFirstTry.

Inductive dcom : Type :=
| DCSkip (P : Assertion)
  (* {{ P }} skip {{ P }} *)
| DCSeq (P : Assertion) (d1 : dcom) (Q : Assertion)
        (d2 : dcom) (R : Assertion)
  (* {{ P }} d1 {{Q}}; d2 {{ R }} *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* etc. *)
| DCIf (P : Assertion) (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
| DCWhile (P : Assertion) (b : bexp)
          (P1 : Assertion) (d : dcom) (P2 : Assertion)
          (Q : Assertion)
| DCPre (P : Assertion) (d : dcom)
| DCPost (d : dcom) (Q : Assertion).

End DComFirstTry.

(** But this would result in _very_ verbose decorated programs with a
    lot of repeated annotations: a simple program like
    [skip;skip] would be decorated like this,

        {{P}} ({{P}} skip {{P}}) ; ({{P}} skip {{P}}) {{P}}

    with pre- and post-conditions around each [skip], plus identical
    pre- and post-conditions on the semicolon! *)

(** In other words, we don't want both preconditions and
    postconditions on each command, because a sequence of two commands
    would contain redundant decorations--the postcondition of the
    first likely being the same as the precondition of the second.

    Instead, our formal syntax of decorated commands will omit
    preconditions whenever possible and embed just postconditions. *)

(** - The [skip] command, for example, is decorated only with its
      postcondition

      skip {{ Q }}

      on the assumption that the precondition will be provided by
      somebody else.

      We carry the same assumption through the other syntactic forms:
      each decorated command is assumed to carry its own postcondition
      within itself but take its precondition from its context in
      which it is used. *)

(** - Sequences [d1 ; d2] need no additional decorations.

      Why?

      Because inside [d2] there will be a postcondition, which also
      serves as the postcondition of [d1;d2].

      Similarly, inside [d1] there will also be a postcondition, which
      additionally serves as the _precondition_ for [d2]. *)

(** - An assignment [X := a] is decorated only with its postcondition:

      X := a {{ Q }}
*)

(** - A conditional [if b then d1 else d2] is decorated with a
      postcondition for the entire statement, as well as preconditions
      for each branch:

      if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }}
*)

(** - A loop [while b do d end] is decorated with its final
      postcondition plus a precondition for the body:

      while b do {{ P }} d end {{ Q }}

      The postcondition embedded in [d] serves as the loop invariant. *)

(** - Implications [->>] can be added as decorations either for a
      precondition...

      ->> {{ P }} d

      ...or for a postcondition:

      d ->> {{ Q }}

      The former is waiting for another precondition to be supplied by
      the context; the latter relies on the postcondition already
      embedded in [d]. *)

(** Putting this all together gives us the formal syntax of decorated
    commands: *)

Inductive dcom : Type :=
| DCSkip (Q : Assertion)
  (* skip {{ Q }} *)
| DCSeq (d1 d2 : dcom)
  (* d1 ; d2 *)
| DCAsgn (X : string) (a : aexp) (Q : Assertion)
  (* X := a {{ Q }} *)
| DCIf (b : bexp) (P1 : Assertion) (d1 : dcom)
       (P2 : Assertion) (d2 : dcom) (Q : Assertion)
  (* if b then {{ P1 }} d1 else {{ P2 }} d2 end {{ Q }} *)
| DCWhile (b : bexp) (P : Assertion) (d : dcom)
          (Q : Assertion)
  (* while b do {{ P }} d end {{ Q }} *)
| DCPre (P : Assertion) (d : dcom)
  (* ->> {{ P }} d *)
| DCPost (d : dcom) (Q : Assertion)
  (* d ->> {{ Q }} *).

(** (We then need to redefine all our Notations to get nice
    concrete syntax for [dcom].) *)

(** To provide the initial precondition that goes at the very top of a
    decorated program, we introduce a new type [decorated]: *)

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> decorated.

(** To avoid clashing with the existing [Notation]s for ordinary
    commands, we introduce these notations in a new grammar scope
    called [dcom]. *)

Declare Scope dcom_scope.
Notation "'skip' '{{' P '}}'" := (DCSkip P)
  (in custom com at level 0,
    P custom assn at level 99,
    format "'[v' 'skip' '/' '{{' P '}}' ']'") : dcom_scope.
Notation "l ':=' a '{{' P '}}'" := (DCAsgn l a P)
  (in custom com at level 0,
    l constr at level 0,
    a custom com at level 85,
    P custom assn at level 99,
    no associativity,
    format "'[v' l  ':='  a '/' '{{'  P  '}}' ']'") : dcom_scope.
Notation "'while' b 'do' '{{' Pbody '}}' d 'end' '{{' Ppost '}}'" := (DCWhile b Pbody d Ppost)
  (in custom com at level 89,
    b custom com at level 99,
    Pbody custom assn at level 99,
    Ppost custom assn at level 99,
    format "'[v' 'while'  b  'do' '/  ' '{{' Pbody '}}' '/  ' d '/' 'end' '/' '{{' Ppost '}}' ']'") : dcom_scope.
Notation "'if' b 'then' {{ P1 }} d1 'else' {{ P2 }} d2 'end' {{ Q }}" := (DCIf b P1 d1 P2 d2 Q)
  (in custom com at level 89,
    b custom com at level 99,
    P1 custom assn at level 99,
    P2 custom assn at level 99,
    Q custom assn at level 99,
    format "'[v' 'if'  b  'then' '/  ' '{{' P1 '}}' '/  ' d1 '/' 'else' '/  ' '{{' P2 '}}' '/  ' d2 '/' 'end' '/' '{{' Q '}}' ']'"): dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
          (in custom com at level 12, right associativity, P custom assn at level 99)
          : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
           (in custom com at level 10, right associativity, P custom assn at level 99)
           : dcom_scope.
Notation "x ; y" := (DCSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : dcom_scope.
Notation "{{ P }} d" := (Decorated P d)
  (in custom com at level 91,
    P custom assn at level 99,
    format "'[v' '{{'  P  '}}' '/' d ']'"): dcom_scope.

Local Open Scope dcom_scope.

Example dec0 : dcom :=
  <{ skip {{ True }} }>.
Example dec1 : dcom :=
  <{ while true do {{ True }} skip {{ True }} end {{ True }} }>.

(** Recall that you can [Set Printing All] to see how all that
    notation is desugared. *)
Set Printing All.
Print dec1.
Unset Printing All.

(** An example [decorated] program that decrements [X] to [0]: *)

Example dec_while : decorated :=
  <{
  {{ True }}
    while X <> 0
    do
                 {{ True /\ (X <> 0) }}
      X := X - 1
                 {{ True }}
    end
  {{ True /\  X = 0}} ->>
  {{ X = 0 }} }>.

(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)

Fixpoint erase (d : dcom) : com :=
  match d with
  | DCSkip _           => CSkip
  | DCSeq d1 d2        => CSeq (erase d1) (erase d2)
  | DCAsgn X a _       => CAsgn X a
  | DCIf b _ d1 _ d2 _ => CIf b (erase d1) (erase d2)
  | DCWhile b _ d _    => CWhile b (erase d)
  | DCPre _ d          => erase d
  | DCPost d _         => erase d
  end.

Definition erase_d (dec : decorated) : com :=
  match dec with
  | Decorated P d => erase d
  end.

(** It is also straightforward to extract the precondition and
    postcondition from a decorated program. *)

Definition precondition_from (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq _ d2              => post d2
  | DCAsgn _ _ Q            => Q
  | DCIf  _ _ _ _ _ Q       => Q
  | DCWhile _ _ _ Q         => Q
  | DCPre _ d               => post d
  | DCPost _ Q              => Q
  end.

Definition postcondition_from (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end.

(** We can then express what it means for a decorated program to be
    correct as follows: *)

Definition outer_triple_valid (dec : decorated) :=
  {{$(precondition_from dec)}} erase_d dec {{$(postcondition_from dec)}}.

(** For example: *)

Example dec_while_triple_correct :
     outer_triple_valid dec_while
   =
     {{ True }}
       while X <> 0 do X := X - 1 end
     {{ X = 0 }}.
Proof. reflexivity. Qed.

(** The outer Hoare triple of a decorated program is just a [Prop];
    thus, to show that it is _valid_, we need to produce a proof of
    this proposition.

    We will do this by extracting "proof obligations" from the
    decorations sprinkled throughout the program.

    These obligations are often called _verification conditions_,
    because they are the facts that must be verified to see that the
    decorations are locally consistent and thus constitute a proof of
    validity of the outer triple. *)

(* ================================================================= *)
(** ** Extracting Verification Conditions *)

(** The function [verification_conditions] takes a decorated command
    [d] together with a precondition [P] and returns a _proposition_
    that, if it can be proved, implies that the triple

     {{P}} erase d {{post d}}

    is valid.

    It does this by walking over [d] and generating a big conjunction
    that includes

    - local consistency checks for each form of command, plus

    - uses of [->>] to bridge the gap between the assertions found
      inside a decorated command and the assertions imposed by the
      external precondition; these uses correspond to applications
      of the consequence rule.

    _Local consistency_ is defined as follows... *)

(** - The decorated command

        skip {{Q}}

      is locally consistent with respect to a precondition [P] if
      [P ->> Q].
*)
(** - The sequential composition of [d1] and [d2] is locally
      consistent with respect to [P] if [d1] is locally consistent with
      respect to [P] and [d2] is locally consistent with respect to
      the postcondition of [d1].

    - An assignment

        X := a {{Q}}

      is locally consistent with respect to a precondition [P] if:

        P ->> Q [X |-> a]
*)
(** - A conditional

        if b then {{P1}} d1 else {{P2}} d2 end {{Q}}

      is locally consistent with respect to precondition [P] if

         (1) [P /\ b ->> P1]

         (2) [P /\ ~b ->> P2]

         (3) [d1] is locally consistent with respect to [P1]

         (4) [d2] is locally consistent with respect to [P2]

         (5) [post d1 ->> Q]

         (6) [post d2 ->> Q]
*)
(** - A loop

        while b do {{Q}} d end {{R}}

      is locally consistent with respect to precondition [P] if:

         (1) [P ->> post d]

         (2) [post d /\ b ->> Q]

         (3) [post d /\ ~b ->> R]

         (4) [d] is locally consistent with respect to [Q]
*)
(** - A command with an extra assertion at the beginning

         ->> {{Q}} d

      is locally consistent with respect to a precondition [P] if:

        (1) [P ->> Q]

        (2) [d] is locally consistent with respect to [Q]
*)
(** - A command with an extra assertion at the end

         d ->> {{Q}}

      is locally consistent with respect to a precondition [P] if:

        (1) [d] is locally consistent with respect to [P]

        (2) [post d ->> Q]
*)

(** With all this in mind, we can write a _verification condition
    generator_ that takes a decorated command and reads off a
    proposition saying that all its decorations are locally
    consistent.

    Formally, since a decorated command is "waiting for its
    precondition" the main VC generator takes a [dcom] plus a given
    preondition as arguments. *)

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q =>
         (P ->> Q)
  | DCSeq d1 d2 =>
         verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn X a Q =>
          P ->> {{ Q [X |-> a] }}
  | DCIf b P1 d1 P2 d2 Q =>
         {{ P /\ b }} ->> P1
      /\ {{ P /\ ~ b }}  ->> P2
      /\ (post d1 ->> Q) /\ (post d2 ->> Q)
      /\ verification_conditions P1 d1
      /\ verification_conditions P2 d2
  | DCWhile b Q d R =>
      (* (post d) is both the loop invariant and the initial
         precondition *)
         (P ->> post d)
      /\ {{ $(post d) /\ b }} ->> Q
      /\ {{ $(post d) /\ ~ b }} ->> R
      /\ verification_conditions Q d
  | DCPre P' d =>
         (P ->> P')
      /\ verification_conditions P' d
  | DCPost d Q =>
         verification_conditions P d
      /\ (post d ->> Q)
  end.

(** The following key theorem states that [verification_conditions]
    does its job correctly.  Not surprisingly, each of the Hoare Logic
    rules plays a critical role at some point in the proof. *)

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} erase d {{ $(post d) }}.
Proof.
  induction d; intros; simpl in *.
  - (* Skip *)
    eapply hoare_consequence_pre.
      + apply hoare_skip.
      + assumption.
  - (* Seq *)
    destruct H as [H1 H2].
    eapply hoare_seq.
      + apply IHd2. apply H2.
      + apply IHd1. apply H1.
  - (* Asgn *)
    eapply hoare_consequence_pre.
      + apply hoare_asgn.
      + assumption.
  - (* If *)
    destruct H as [HPre1 [HPre2 [Hd1 [Hd2 [HThen HElse] ] ] ] ].
    apply IHd1 in HThen. clear IHd1.
    apply IHd2 in HElse. clear IHd2.
    apply hoare_if.
      + eapply hoare_consequence; eauto.
      + eapply hoare_consequence; eauto.
  - (* While *)
    destruct H as [Hpre [Hbody1 [Hpost1  Hd] ] ].
    eapply hoare_consequence; eauto.
    apply hoare_while.
    eapply hoare_consequence_pre; eauto.
  - (* Pre *)
    destruct H as [HP Hd].
    eapply hoare_consequence_pre; eauto.
  - (* Post *)
    destruct H as [Hd HQ].
    eapply hoare_consequence_post; eauto.
Qed.

(** Now that all the pieces are in place, we can define what it means
    to verify an entire program. *)

Definition verification_conditions_from
              (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end.

(** And this brings us to the main theorem of this section: *)

Corollary verification_conditions_correct : forall dec,
  verification_conditions_from dec ->
  outer_triple_valid dec.
Proof.
  intros [P d]. apply verification_correct.
Qed.

(* ================================================================= *)
(** ** More Automation *)

(** The propositions generated by [verification_conditions] are fairly
    big and contain many conjuncts that are essentially trivial. *)

Eval simpl in verification_conditions_from dec_while.
(* ==>
   ((fun _ : state => True) ->>
           (fun _ : state => True)) /\
   ((fun st : state => True /\ negb (st X =? 0) = true) ->>
           (fun st : state => True /\ st X <> 0)) /\
   ((fun st : state => True /\ negb (st X =? 0) <> true) ->>
           (fun st : state => True /\ st X = 0)) /\
   (fun st : state => True /\ st X <> 0) ->>
           (fun _ : state => True) [X |-> X - 1]) /\
   (fun st : state => True /\ st X = 0) ->>
           (fun st : state => st X = 0)
: Prop
*)

(** Fortunately, our [verify_assertion] tactic can generally take care of
    most (or sometimes all) of them. *)
Example vc_dec_while : verification_conditions_from dec_while.
Proof. verify_assertion. Qed.

(** To automate the overall process of verification, we can use
    [verification_correct] to extract the verification conditions, use
    [verify_assertion] to verify them as much as it can, and finally tidy
    up any remaining bits by hand.  *)
Ltac verify :=
  intros;
  apply verification_correct;
  verify_assertion.

(** Here's the final, formal proof that dec_while is correct. *)

Theorem dec_while_correct :
  outer_triple_valid dec_while.
Proof. verify. Qed.

(* ################################################################# *)
(** * Finding Loop Invariants *)

(** Once the outer pre- and postcondition are chosen, the only
    creative part in verifying programs using Hoare Logic is finding
    the right loop invariants... *)

(* ================================================================= *)
(** ** Example: Slow Subtraction *)

(** The following program subtracts the value of [X] from the value of
    [Y] by repeatedly decrementing both [X] and [Y].  We want to verify its
    correctness with respect to the pre- and postconditions shown:

           {{ X = m /\ Y = n }}
             while X <> 0 do
               Y := Y - 1;
               X := X - 1
             end
           {{ Y = n - m }}
*)

(** To verify this program, we need to find an invariant [Inv] for the
    loop.  As a first step we can leave [Inv] as an unknown and build a
    _skeleton_ for the proof by applying the rules for local
    consistency, working from the end of the program to the beginning,
    as usual, and without doing any thinking at all yet. *)

(** This leads to the following skeleton:

        (1)    {{ X = m /\ Y = n }}  ->>                   (a)
        (2)    {{ Inv }}
                 while X <> 0 do
        (3)              {{ Inv /\ X <> 0 }}  ->>          (c)
        (4)              {{ Inv [X |-> X-1] [Y |-> Y-1] }}
                   Y := Y - 1;
        (5)              {{ Inv [X |-> X-1] }}
                   X := X - 1
        (6)              {{ Inv }}
                 end
        (7)    {{ Inv /\ ~ (X <> 0) }}  ->>                (b)
        (8)    {{ Y = n - m }}
*)
(** Examining this skeleton, we can see that any valid [Inv] will
    have to respect three conditions:
    - (a) it must be _weak_ enough to be implied by the loop's
      precondition, i.e., (1) must imply (2);
    - (b) it must be _strong_ enough to imply the program's postcondition,
      i.e., (7) must imply (8);
    - (c) it must be _preserved_ by a single iteration of the loop, assuming
      that the loop guard also evaluates to true, i.e., (3) must imply (4). *)

(* WORK IN CLASS (by filling in the previous template) *)
(* ================================================================= *)
(** ** Example: Parity *)

(** Here is a cute way of computing the parity of a value initially
    stored in [X], due to Daniel Cristofani.

       {{ X = m }}
         while 2 <= X do
           X := X - 2
         end
       {{ X = parity m }}

    The [parity] function used in the specification is defined in
    Rocq as follows: *)

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end.

Definition parity_dec (m:nat) : decorated :=
  <{
  {{ X = m }} ->>
  {{ FILL_IN_HERE }}
    while 2 <= X do
                  {{ FILL_IN_HERE }} ->>
                  {{ FILL_IN_HERE }}
      X := X - 2
                  {{ FILL_IN_HERE }}
    end
  {{ FILL_IN_HERE }} ->>
  {{ X = #parity m }} }>.

(* ================================================================= *)
(** ** Example: Finding Square Roots *)

(** The following program computes the integer square root of [X]
    by naive iteration:

    {{ X=m }}
      Z := 0;
      while (Z+1)*(Z+1) <= X do
        Z := Z+1
      end
    {{ Z*Z<=m /\ m<(Z+1)*(Z+1) }}
*)

(* WORK IN CLASS *)

(* ================================================================= *)
(** ** Example: Squaring *)

(** Here is a program that squares [X] by repeated addition:

  {{ X = m }}
    Y := 0;
    Z := 0;
    while Y <> X  do
      Z := Z + X;
      Y := Y + 1
    end
  {{ Z = m*m }}
*)

(* WORK IN CLASS *)

(** [] *)


(* ################################################################# *)
(** * Weakest Preconditions (Optional) *)

(** A useless (though valid) Hoare triple:

      {{ False }}  X := Y + 1  {{ X <= 5 }}

    A better precondition:

      {{ Y <= 4 /\ Z = 0 }}  X := Y + 1 {{ X <= 5 }}

    The _best_ precondition:

      {{ Y <= 4 }}  X := Y + 1  {{ X <= 5 }}
*)

(** Assertion [Y <= 4] is a _weakest precondition_ of command [X :=
    Y + 1] with respect to postcondition [X <= 5].  Think of _weakest_
    here as meaning "easiest to satisfy": a weakest precondition is
    one that as many states as possible can satisfy. *)

(** [P] is a weakest precondition of command [c] for postcondition [Q]
    if

      - [P] is a precondition, that is, [{{P}} c {{Q}}]; and
      - [P] is at least as weak as all other preconditions, that is,
        if [{{P'}} c {{Q}}] then [P' ->> P].
 *)

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

(** **** Exercise: 1 star, standard, optional (wp)

    What are weakest preconditions of the following commands
    for the following postconditions?

  1) {{ ? }}  skip  {{ X = 5 }}

  2) {{ ? }}  X := Y + Z {{ X = 5 }}

  3) {{ ? }}  X := Y  {{ X = Y }}

  4) {{ ? }}
     if X = 0 then Y := Z + 1 else Y := W + 2 end
     {{ Y = 5 }}

  5) {{ ? }}
     X := 5
     {{ X = 0 }}

  6) {{ ? }}
     while true do X := 0 end
     {{ X = 0 }}
*)
(* FILL IN HERE

    [] *)


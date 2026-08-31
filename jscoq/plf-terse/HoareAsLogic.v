(** * HoareAsLogic: Hoare Logic as a Logic *)

(** The presentation of Hoare logic in chapter [Hoare] could be
    described as "model-theoretic": the proof rules for each of the
    constructors were presented as _theorems_ about the evaluation
    behavior of programs, and proofs of program correctness (validity
    of Hoare triples) were constructed by combining these theorems
    directly in Rocq.

    Another way of presenting Hoare logic is to define a completely
    separate proof system -- a set of axioms and inference rules that
    talk about commands, Hoare triples, etc. -- and then say that a
    proof of a Hoare triple is a valid derivation in _that_ logic.  We
    can do this by giving an inductive definition of _valid
    derivations_ in this new logic.

    This chapter is optional.  Before reading it, you'll want to read
    the [ProofObjects] chapter in _Logical
    Foundations_ (_Software Foundations_, volume 1). *)

Set Warnings "-deprecated-hint-without-locality,-deprecated-hint-without-locality,-parsing".
From PLF Require Import Maps.
From PLF Require Import Hoare.

Hint Constructors ceval : core.

(* ################################################################# *)
(** * Hoare Logic and Model Theory *)

(** A _valid_ Hoare triple expresses a truth about how Imp
    program execute. *)

Definition valid (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st'  ->
     P st  ->
     Q st'.

(** So far, we have punned between the syntax of a Hoare triple,
    written [{{P}} c {{Q}}], and its validity, as expressed by
    [valid].  In essence, we have said that the semantic meaning of
    that syntax is the proposition returned by [valid].  This way of
    giving semantic meaning to something syntactic is part of the
    branch of mathematical logic known as _model theory_.  *)

(* ################################################################# *)
(** * Hoare Logic and Proof Theory *)

(** Proof rules constitute a logic in their own right: *)

(**

             ----------------  (hoare_skip)
             {{P}} skip {{P}}

             ----------------------------- (hoare_asgn)
             {{Q [X |-> a]}} X := a {{Q}}

               {{P}} c1 {{Q}}
               {{Q}} c2 {{R}}
              ------------------  (hoare_seq)
              {{P}} c1; c2 {{R}}

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}

            {{P /\ b}} c {{P}}
      ----------------------------- (hoare_while)
      {{P} while b do c end {{P /\ ~b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

(** Those rules can be used to show that a triple is _derivable_
    by constructing a proof tree: *)

(**

                    ---------------------------  (hoare_asgn)
   X=0 ->> X+1=1    {{X+1=1}} X := X+1 {{X=1}}
   -------------------------------------------------------  (hoare_consequence)
                     {{X=0}} X := X+1 {{X=1}}
*)

(** This approach gives meaning to triples not in terms of a model,
    but in terms of how they can be used to construct proof trees.
    It's a different way of giving semantic meaning to something
    syntactic, and it's part of the branch of mathematical logic known
    as _proof theory_.

    Our goal for the rest of this chapter is to formalize Hoare logic
    using proof theory, and then to prove that the model-theoretic and
    proof-theoretic formalizations are consistent with one another.
*)

(* ################################################################# *)
(** * Derivability *)

(** To formalize derivability of Hoare triples, we introduce inductive type
    [derivable], which describes legal proof trees using the Hoare rules. *)

Inductive derivable : Assertion -> com -> Assertion -> Type :=
  | H_Skip : forall P,
      derivable P <{skip}> P
  | H_Asgn : forall Q V a,
      derivable ({{Q [V |-> a]}}) <{V := a}> Q
  | H_Seq : forall P c Q d R,
      derivable Q d R -> derivable P c Q -> derivable P <{c;d}> R
  | H_If : forall P Q b c1 c2,
    derivable (fun st => P st /\ bassertion b st) c1 Q ->
    derivable (fun st => P st /\ ~(bassertion b st)) c2 Q ->
    derivable P <{if b then c1 else c2 end}> Q
  | H_While : forall P b c,
    derivable (fun st => P st /\ bassertion b st) c P ->
    derivable P <{while b do c end}> (fun st => P st /\ ~ (bassertion b st))
  | H_Consequence : forall (P Q P' Q' : Assertion) c,
    derivable P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.

(** As an example, let's construct a proof tree for

        {{(X=3) [X |-> X + 2] [X |-> X + 1]}}
      X := X + 1;
      X := X + 2
        {{X=3}}
*)

Example sample_proof :
  derivable
    ({{ $(fun st:state => st X = 3)  [X |-> X + 2] [X |-> X + 1] }})
    <{ X := X + 1; X := X + 2}>
    (fun st:state => st X = 3).
Proof.
  eapply H_Seq.
  - apply H_Asgn.
  - apply H_Asgn.
Qed.

(** You can see how the structure of the proof script mirrors the structure
    of the proof tree: at the root there is a use of the sequence rule; and
    at the leaves, the assignment rule. *)

(* ################################################################# *)
(** * Soundness and Completeness *)

(** We now have two approaches to formulating Hoare logic:

    - The model-theoretic approach uses [valid] to characterize when a Hoare
      triple holds in a model, which is based on states.

    - The proof-theoretic approach uses [derivable] to characterize when a Hoare
      triple is derivable as the end of a proof tree.

    Do these two approaches agree?  That is, are the valid Hoare triples exactly
    the derivable ones?  This is a standard question investigated in
    mathematical logic.  There are two pieces to answering it:

    - A logic is _sound_ if everything that is derivable is valid.

    - A logic is _complete_ if everything that is valid is derivable.

    We can prove that Hoare logic is sound and complete.

*)

(* ################################################################# *)
(** * Postscript: Decidability *)

(** We might hope that Hoare logic would be _decidable_; that is, that
    there would be an (terminating) algorithm (a _decision procedure_)
    that can determine whether or not a given Hoare triple is valid or
    derivable.  Sadly, such a decision procedure cannot exist.

    Consider the triple [{{True}} c {{False}}]. This triple is valid
    if and only if [c] is non-terminating.  So any algorithm that
    could determine validity of arbitrary triples could solve the
    Halting Problem.

    Similarly, the triple [{{True}} skip {{P}}] is valid if and only
    if [forall s, P s] is valid, where [P] is an arbitrary assertion
    of Rocq's logic. But this logic is far too powerful to be
    decidable. *)


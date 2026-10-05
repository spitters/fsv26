(** * StlcProp: Properties of STLC *)

(*
                  THE SIMPLY TYPED LAMBDA CALCULUS

    Syntax:

       t ::= x                         variable
           | \x:T,t                    abstraction
           | t t                       application
           | true                      constant true
           | false                     constant false
           | if t then t else t        conditional

    Values:

       v ::= \x:T,t
           | true
           | false

    Substitution:

       [x:=s]x               = s
       [x:=s]y               = y                      if x <> y
       [x:=s](\x:T, t)       = \x:T, t
       [x:=s](\y:T, t)       = \y:T, [x:=s]t          if x <> y
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)
       [x:=s]true            = true
       [x:=s]false           = false
       [x:=s](if t1 then t2 else t3) =
                       if [x:=s]t1 then [x:=s]t2 else [x:=s]t3

    Small-step operational semantics:

                               value v2
                     ---------------------------                    (ST_AppAbs)
                     (\x:T2,t1) v2 --> [x:=v2]t1

                              t1 --> t1'
                           ----------------                           (ST_App1)
                           t1 t2 --> t1' t2

                              value v1
                              t2 --> t2'
                           ----------------                           (ST_App2)
                           v1 t2 --> v1 t2'

                    --------------------------------                (ST_IfTrue)
                    (if true then t1 else t2) --> t1

                    ---------------------------------              (ST_IfFalse)
                    (if false then t1 else t2) --> t2

                              t1 --> t1'
         ----------------------------------------------------           (ST_If)
         (if t1 then t2 else t3) --> (if t1' then t2 else t3)

    Typing:

                              Gamma x = T1
                            ------------------                          (T_Var)
                            Gamma |-- x \in T1

                        x |-> T2 ; Gamma |-- t1 \in T1
                        ------------------------------                  (T_Abs)
                         Gamma |-- \x:T2,t1 \in T2->T1

                         Gamma |-- t1 \in T2->T1
                           Gamma |-- t2 \in T2
                         -----------------------                        (T_App)
                         Gamma |-- t1 t2 \in T1

                         -----------------------                        (T_True)
                         Gamma |-- true \in Bool

                         ------------------------                       (T_False)
                         Gamma |-- false \in Bool

    Gamma |-- t1 \in Bool    Gamma |-- t2 \in T1   Gamma |-- t3 \in T1
    ------------------------------------------------------------------  (T_If)
                  Gamma |-- if t1 then t2 else t3 \in T1
*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Stlc.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".
Module STLCProp.
Import STLC.

(** In this chapter, we develop the fundamental theory of the Simply
    Typed Lambda Calculus -- in particular, the type safety
    theorem. *)

(* ################################################################# *)
(** * Canonical Forms *)

(** Formally, we will need these lemmas only for terms that are not
    only well typed but _closed_ -- i.e., well typed in the empty
    context. *)

Lemma canonical_forms_bool : forall t,
  <{ empty |-- t \in Bool }> ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t HT HVal.
  destruct HVal; auto.
  inversion HT.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  <{ empty |-- t \in T1 -> T2 }> ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal as [x ? t1| |] ; inversion HT; subst.
  exists x, t1. reflexivity.
Qed.

(* ################################################################# *)
(** * Progress *)

(** The _progress_ theorem tells us that closed, well-typed
    terms are not stuck. *)

Theorem progress : forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst Gamma; auto.
  (* auto solves all three cases in which t is a value *)
  - (* T_Var *)
    (* contradictory: variables cannot be typed in an
       empty context *)
    discriminate H.

  - (* T_App *)
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a
       value or steps... *)
    right. destruct IHHt1...
    + (* t1 is a value *)
      destruct IHHt2...
      * (* t2 is also a value *)
        eapply canonical_forms_fun in Ht1; [|assumption].
        destruct Ht1 as [x [t0 H1]]. subst.
        exists (<{ [x:=t2]t0 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists (<{t1 t2'}>)...

    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists (<{t1' t2}>)...

  - (* T_If *)
    right. destruct IHHt1...

    + (* t1 is a value *)
      destruct (canonical_forms_bool t1); subst; eauto.

    + (* t1 also steps *)
      destruct H as [t1' Hstp]. exists <{if t1' then t2 else t3}>...
Qed.

(* ################################################################# *)
(** * Preservation *)

(** For preservation, we need some technical machinery for reasoning
    about variables and substitution.

      - The _preservation theorem_ is proved by induction on a typing
        derivation and case analysis on the step relation,
        pretty much as we did in the [Types] chapter.

        Main novelty: [ST_AppAbs] uses the substitution operation.

        To see that this step preserves typing, we need to know that
        the substitution itself does.  So we prove a...

      - _substitution lemma_, stating that substituting a (closed,
        well-typed) term [s] for a variable [x] in a term [t]
        preserves the type of [t].

        The proof goes by induction on the form of [t] and requires
        looking at all the different cases in the definition of
        substitition.

        Tricky case: variables.

        In this case, we need to deduce from the fact that a term [s]
        has type S in the empty context the fact that [s] has type S
        in every context.

        For this we prove a...*)
(**   - _weakening_ lemma, showing that typing is preserved under
        "extensions" to the context [Gamma].

    To make Rocq happy, we need to formalize all this in the opposite
    order... *)

(* ================================================================= *)
(** ** The Weakening Lemma *)

(** First, we show that typing is preserved under "extensions" to the
    context [Gamma].  (Recall the definition of "includedin" from
    Maps.v.) *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     <{ Gamma  |-- t \in T }>  ->
     <{ Gamma' |-- t \in T }>.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

(** The following simple corollary is what we actually need below. *)

Lemma weakening_empty : forall Gamma t T,
     <{ empty |-- t \in T }> ->
     <{ Gamma |-- t \in T }>.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* ================================================================= *)
(** ** The Substitution Lemma *)

(** Now we come to the conceptual heart of the proof that reduction
    preserves types -- namely, the observation that _substitution_
    preserves types. *)

(** The _substitution lemma_ says:

    - Suppose we have a term [t] with a free variable [x], and
      suppose we've been able to assign a type [T] to [t] under the
      assumption that [x] has some type [U].

    - Also, suppose that we have some other term [v] and that we've
      shown that [v] has type [U].

    - Then we can substitute [v] for each of the occurrences of
      [x] in [t] and obtain a new term that still has type [T]. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
  <{ x |-> U ; Gamma |-- t \in T }> ->
  <{ empty |-- v \in U }>  ->
  <{ Gamma |-- [x:=v]t \in T }>.

Proof.
  intros Gamma x U t v T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
  (* in each case, we'll want to get at the derivation of H *)
    inversion H; clear H; subst; simpl; eauto.
  - (* var *)
    rename s into y. destruct (eqb_spec x y); subst.
    + (* x=y *)
      rewrite update_eq in H2.
      injection H2 as H2; subst.
      apply weakening_empty. assumption.
    + (* x<>y *)
      apply T_Var. rewrite update_neq in H2; auto.
  - (* abs *)
    rename s into y, t into S.
    destruct (eqb_spec x y); subst; apply T_Abs.
    + (* x=y *)
      rewrite update_shadow in H5. assumption.
    + (* x<>y *)
      apply IHt.
      rewrite update_permute; auto.
Qed.

(* ================================================================= *)
(** ** Main Theorem *)

(** We now have the ingredients we need to prove preservation: if a
    closed, well-typed term [t] has type [T] and takes a step to [t'],
    then [t'] is also a closed term with type [T].  In other words,
    the small-step reduction relation preserves types. *)

Theorem preservation : forall t t' T,
  <{ empty |-- t \in T }> ->
  t --> t'  ->
  <{ empty |-- t' \in T }>.

Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; auto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      apply substitution_preserves_typing with T2...
      inversion HT1...
Qed.

End STLCProp.


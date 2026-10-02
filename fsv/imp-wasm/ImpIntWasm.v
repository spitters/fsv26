From Stdlib Require Import Uint63 String.
From LF Require Import ImpInt.
From Peregrine.Plugin Require Import Loader.
Open Scope uint63_scope.

(* uint63_scope is open for the numerals, so the variable names are tagged *)
Definition sX : string := "X"%string.
Definition sY : string := "Y"%string.
Definition sZ : string := "Z"%string.

(* fact_in_coq of Imp.v, restated with the constructors of ImpInt *)
Definition fact_prog : com :=
  CSeq (CAsgn sZ (AId sX))
       (CSeq (CAsgn sY (ANum 1))
             (CWhile (BNeq (AId sZ) (ANum 0))
                     (CSeq (CAsgn sY (AMult (AId sY) (AId sZ)))
                           (CAsgn sZ (AMinus (AId sZ) (ANum 1)))))).

Definition run_fact (n : int) : int :=
  match ceval_step (update empty_st sX n) fact_prog 200 with
  | Some st => st sY
  | None => 0
  end.

Definition ifact8 : int := run_fact 8.
Definition ifact12 : int := run_fact 12.
Definition ifact20 : int := run_fact 20.

(* subtract_slowly of Imp.v *)
Definition slow_prog : com :=
  CWhile (BNeq (AId sX) (ANum 0))
         (CSeq (CAsgn sZ (AMinus (AId sZ) (ANum 1)))
               (CAsgn sX (AMinus (AId sX) (ANum 1)))).

Definition islow : int :=
  match ceval_step (update (update empty_st sX 1000) sZ 5000) slow_prog 4000 with
  | Some st => st sZ
  | None => 0
  end.

Peregrine Extract "ast/ifact8.ast" ifact8.
Peregrine Extract "ast/ifact12.ast" ifact12.
Peregrine Extract "ast/ifact20.ast" ifact20.
Peregrine Extract "ast/islow.ast" islow.

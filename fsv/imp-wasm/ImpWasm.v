(** Drivers for the browser demo: the LF chapters' own Imp programs, run by
    [ImpCEvalFun.ceval_step] and extracted to WebAssembly by Peregrine.
    Each extracted term is a closed [nat], which is what the module's
    [main_function] computes and the page decodes out of linear memory. *)

From LF Require Import Maps Imp ImpCEvalFun.
From Peregrine.Plugin Require Import Loader.

(** [fact_in_coq] (Imp.v) with X := n; the factorial ends up in Y. *)
Definition run_fact (n : nat) : nat :=
  match ceval_step (X !-> n) fact_in_coq 10000 with
  | Some st => st Y
  | None => 0
  end.

Definition fact5 : nat := run_fact 5.
Definition fact7 : nat := run_fact 7.

(** [subtract_slowly] (Imp.v): 1000 iterations, but the numbers stay small,
    so this one is bounded by the step budget rather than by the stack. *)
Definition slow : nat :=
  match ceval_step (Z !-> 5000; X !-> 1000) subtract_slowly 50000 with
  | Some st => st Z
  | None => 0
  end.

(** The conditional program of [example_test_ceval] (ImpCEvalFun.v); Z ends
    up 4, since X is 2 and the guard X <= 1 is false. *)
Definition cond_prog : com :=
  <{ X := 2;
     if (X <= 1)
     then Y := 3
     else Z := 4
     end }>.

Definition cond : nat :=
  match ceval_step empty_st cond_prog 10000 with
  | Some st => st Z
  | None => 0
  end.

Peregrine Extract "ast/fact5.ast" fact5.
Peregrine Extract "ast/fact7.ast" fact7.
Peregrine Extract "ast/slow.ast" slow.
Peregrine Extract "ast/cond.ast" cond.

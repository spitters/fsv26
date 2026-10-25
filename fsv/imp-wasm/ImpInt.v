(** Imp over machine integers.

    This is the Imp of the Logical Foundations chapters with [nat] replaced by
    [Uint63.int], so that the extracted code does machine arithmetic. The
    definitions mirror [Imp.aeval] / [Imp.beval] / [ImpCEvalFun.ceval_step]
    line for line, but nothing is proved about them here: the chapter's
    [ceval_and_ceval_step_coincide] is about the [nat] version, and does not
    transfer, since [int] wraps at 2^63 where [nat] does not.

    [AMinus] keeps nat's truncated subtraction; int63 subtraction wraps. The
    step index stays a [nat], as in the chapter, so [ceval_step] is still
    structurally recursive. *)

From Stdlib Require Import Uint63 String.
Open Scope uint63_scope.

Definition state := string -> int.
Definition empty_st : state := fun _ => 0.
Definition update (st : state) (x : string) (v : int) : state :=
  fun y => if String.eqb x y then v else st y.

Inductive aexp : Type :=
  | ANum (n : int)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Definition sub_trunc (a b : int) : int :=
  if Uint63.ltb a b then 0 else Uint63.sub a b.

Fixpoint aeval (st : state) (a : aexp) : int :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => Uint63.add (aeval st a1) (aeval st a2)
  | AMinus a1 a2 => sub_trunc (aeval st a1) (aeval st a2)
  | AMult a1 a2 => Uint63.mul (aeval st a1) (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => Uint63.eqb (aeval st a1) (aeval st a2)
  | BNeq a1 a2 => negb (Uint63.eqb (aeval st a1) (aeval st a2))
  | BLe a1 a2 => Uint63.leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Fixpoint ceval_step (st : state) (c : com) (i : nat) : option state :=
  match i with
  | O => None
  | S i' =>
      match c with
      | CSkip => Some st
      | CAsgn l a1 => Some (update st l (aeval st a1))
      | CSeq c1 c2 =>
          match ceval_step st c1 i' with
          | Some st' => ceval_step st' c2 i'
          | None => None
          end
      | CIf b c1 c2 =>
          if beval st b then ceval_step st c1 i' else ceval_step st c2 i'
      | CWhile b1 c1 =>
          if beval st b1 then
            match ceval_step st c1 i' with
            | Some st' => ceval_step st' c i'
            | None => None
            end
          else Some st
      end
  end.

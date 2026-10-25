(** In these exercises we will practice equations by working with
    different implementations of vectors and matrices. The exercises
    are marked with stars, where 1 star exercises are the simplest
    and exercises with more start are more complicated.

    In order to complete some of the exercises you may need to define
    your own additional definitions/lemmas. *)

(** The following Axiom [todo] is used as a place holder. In exercises
    where the Axiom [todo] is used, you are supposed to replace [todo]
    with your own implementation. *)

Axiom todo : forall {A}, A.

From Equations Require Import Equations.
Require Import Logic.FunctionalExtensionality.

(* This exposes the [extensionality f] tactic, 
which applies the funext lemma and does some cleanup.*)

(** Recall our definition of [vec] as an inductive type. *)

Inductive vec (A:Type) : nat -> Type := 
  | nil : vec A 0
  | cons : forall n, A -> vec A n -> vec A (S n).

Arguments nil {A}.
Arguments cons {A n}.

(** We derive [Signature] for [vec] here, so that the equations
    plugin will not reprove this every time it is needed. *)

Derive Signature for vec.

(** We will be using the following notations for convenience. *)

Notation "x :: v" := (cons x v).
Notation "[ ]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) .. )).

(** Recall our definitions of [head], [tail] and [decompose]. *)

Equations head {A n} (v : vec A (S n)) : A :=
head (x :: _) := x.

Equations tail {A n} (v : vec A (S n)) : vec A n :=
tail (_ :: v) := v.

Equations decompose {A n} (v : vec A (S n)) : v = cons (head v) (tail v) :=
decompose (x :: v) := eq_refl.

(** We can implement [app1], the function which adds one element
    to the end of a vector. *)

Equations app1 {A n} (v : vec A n) (x : A) : vec A (S n) :=
app1 [] y := [y];
app1 (x :: v') y := x :: app1 v' y.

Example app1_nil : app1 [] 0 = [0].
Proof.
  reflexivity.
Qed.

Example app1_2 : app1 [0;1] 2 = [0;1;2].
Proof.
  reflexivity.
Qed.

(** Exercise, 2 star: Finish the definition of [rev], the function
    which reverses a vector. *)

Equations rev {A n} (v : vec A n) : vec A n :=
rev _ := todo.

(** Exercise, 1 star: Show that [rev] satisfies the examples [rev_0]
    and [rev_3] below. *)

Example rev_0 : rev (@nil nat) = nil.
Proof.
Admitted.

Example rev_3 : rev [0;1;2] = [2;1;0].
Proof.
Admitted.

(** Exercise, 2 star: Finish the following proof that a vector with
    zero elements is [nil]. *)

Equations vec0_is_nil {A} (v : vec A 0) : v = nil :=
vec0_is_nil _ := todo.

(** Exercise, 3 star: Prove that [rev] is an involution [rev_involution]. *)

Lemma rev_involution {A n} (v : vec A n) : rev (rev v) = v.
Proof.
Admitted.

(** We can implement the type [fin n] of numbers strictly less than
    [n : nat] with the following inductive definition. *)

Inductive fin : nat -> Set :=
  | f0 : forall n, fin (S n)
  | fS : forall n, fin n -> fin (S n).

Derive Signature for fin.

Arguments f0 {n}.
Arguments fS {n}.

(** For example, [fin 3] has the following inhabitants: *)

Check f0 : fin 3.
Check fS f0 : fin 3.
Check fS (fS f0) : fin 3.

(** But [fS (fS (fS f0))] is not an inhabitant of [fin 3]: *)

Fail Check fS (fS (fS f0)) : fin 3.

(** The following definition [fvec] is an alternative way to define a
    vector data type. *)

Definition fvec (A:Type) (n : nat) : Type := fin n -> A.

(** The head of an [fvec] is given by the element at [f0]. *)

Definition fhead {A:Type} {n} (v : fvec A (S n)) : A := v f0.

(** The definition [ftail] gives the tail of an [fvec]. *)

Definition ftail {A} {n} (v : fvec A (S n)) (i : fin n) : A := v (fS i).

(** Notice that the following check succeeds. *)

Check @ftail : forall A n, fvec A (S n) -> fvec A n.

(** Exercise, 2 star: Finish the following definition of [fnil], which
    is the [fvec A 0] corresponding to [nil : vec A 0]. *)

Equations fnil {A:Type} (i : fin 0) : A :=
fnil _ := todo.

(** The following check should succeed. *)

Check @fnil : forall A, fvec A 0.

(** Exercise, 2 star: Finish the following definition of [fcons], which
    is the [fvec A (S n)] corresponding to [cons : vec A (S n)]. *)

Equations fcons {A:Type} {n} (x : A) (v : fvec A n) (i : fin (S n)) : A :=
fcons _ _ _ := todo.

(** The following check should succeed. *)

Check @fcons : forall A n, A -> fvec A n -> fvec A (S n).

(** Exercise, 1 star: To test your implementation of [fnil] and [fcons],
    prove the examples [fidx_0], [fidx_1], [fidx_2]. *)

Example fidx_0 : (fcons 0 (fcons 1 (fcons 2 fnil))) f0 = 0.
Proof.
Admitted.

Example fidx_1 : (fcons 0 (fcons 1 (fcons 2 fnil))) (fS f0) = 1.
Proof.
Admitted.

Example fidx_2 : (fcons 0 (fcons 1 (fcons 2 fnil))) (fS (fS f0)) = 2.
Proof.
Admitted.

(** Exercise, 2 star: Finish the definition of [vec_to_fvec], which is
    the function for indexing a [vec], i.e. [vec_to_fvec v i] is the
    element at index [i] in vector [v]. *)

Equations vec_to_fvec {A n} (v : vec A n) (i : fin n) : A :=
vec_to_fvec _ _ := todo.

(** Notice that [@vec_to_fvec A n] is a function mapping a [vec A n]
    to an [fvec A n]. *)

Check @vec_to_fvec : forall A n, vec A n -> fvec A n.

(** Exercise, 1 star: To test, prove the examples
    [idx_0], [idx_1], [idx_2]. *)

Example idx_0 : vec_to_fvec [0;1;2] f0 = 0.
Proof.
Admitted.

Example idx_1 : vec_to_fvec [0;1;2] (fS f0) = 1.
Proof.
Admitted.

Example idx_2 : vec_to_fvec [0;1;2] (fS (fS f0)) = 2.
Proof.
Admitted.

(** Exercise, 3 star: Finish [fvec_to_vec], the inverse of [vec_to_fvec].
    It is the unique function satisfying the Lemmas [section_vec_to_fvec]
    and [retract_vec_to_fvec] below. *)

Equations fvec_to_vec {A:Type} {n} (v : fvec A n) : vec A n :=
fvec_to_vec _ := todo.

(** Exercise, 3 star: Finish the following lemma [section_vec_to_fvec]. *)

Lemma section_vec_to_fvec
  : forall {A n} (v : vec A n), fvec_to_vec (vec_to_fvec v) = v.
Proof.
Admitted.

(** Exercise, 3 star: Finish the following lemma [retract_vec_to_fvec']. *)

Lemma retract_vec_to_fvec'
  : forall {A n} (v : fvec A n) (i : fin n),
      vec_to_fvec (fvec_to_vec v) i = v i.
Proof.
Admitted.

(** Exercise, 2 star: Finish lemma [retract_vec_to_fvec].
    Hint: The tactic [extensionality f] applies the functional 
          extensionality axiom. *)

Lemma retract_vec_to_fvec
  : forall {A n} (v : fvec A n), vec_to_fvec (fvec_to_vec v) = v.
Proof.
Admitted.

(** Exercise, 3 star: The Lemmas [vec_to_fvec] and [fvec_to_vec] show that
    there is a bijective correspondence between [vec A n] and [fvec A n].
    Finish the examples [nil_to_fnil], [cons_to_fcons], [fnil_to_nil]
    and [fcons_to_cons] to show that your implementation of [fnil] and
    [fcons] corresponds to [nil] and [cons], respectively, under this
    bijective correspondence. *)

Lemma nil_to_fnil : forall A, vec_to_fvec (@nil A) = fnil.
Proof.
Admitted.

Lemma cons_to_fcons
  : forall {A n} (x : A) (v : vec A n),
      vec_to_fvec (cons x v) = fcons x (vec_to_fvec v).
Proof.
Admitted.

Lemma fnil_to_nil A : fvec_to_vec (@fnil A) = nil.
Proof.
Admitted.

Lemma fcons_to_cons
  : forall {A n} (x : A) (v : fvec A n),
      fvec_to_vec (fcons x v) = cons x (fvec_to_vec v).
Proof.
Admitted.

(** Exercise, 2 star. Finish the definition of [map], such that
    [map f [x1; x2; ...; xn] = [f x1; f x2; ...; f x3]]. *)

Equations map {A B n} (f : A -> B) (v : vec A n) : vec B n :=
map _ _ := todo.

(** Exercise, 3 star. Show that [map] is correct by proving
    Lemma [vec_to_fvec_map]. *)
(* Hint: The [depelim i] tactic is a dependent version of [induction].
   It may be useful in the second case of the induction.*)
Lemma vec_to_fvec_map :
  forall {A B n} (f : A -> B) (v : vec A n) (i : fin n),
    vec_to_fvec (map f v) i = f (vec_to_fvec v i).
Proof.
intros A B n f v i.
  induction v.
Admitted.

(** Exercise, 2 star. Finish [replicate], such that
    [replicate n x : vec A n] is the vector where all elements are [x]. *)

Equations replicate {A} (n : nat) (x : A) : vec A n :=
replicate _ _ := todo.

(** Exercise, 3 star. Show that [replicate] is correct by proving
    Lemma [vec_to_fvec_replicate]. *)

Lemma vec_to_fvec_replicate :
  forall {A} (n : nat) (x : A) (i : fin n),
    vec_to_fvec (replicate n x) i = x.
Proof.
Admitted.

(** Exercise, 3 star. Prove Lemma [replicate_app1]. *)

Lemma replicate_app1 :
  forall {A} (n : nat) (x : A),
    replicate (S n) x = app1 (replicate n x) x.
Proof.
Admitted.

(** Exercise, 3 star. Prove Lemma [rev_replicate]. *)

Lemma rev_replicate :
  forall {A} (n : nat) (x : A),
    rev (replicate n x) = replicate n x.
Proof.
Admitted.

(** Exercise, 3 star. Finish the definition of [remove_last].
    Hint: the obvious way of defining [remove_last] might require to use [by wf ...] due to limitations of Equations.
    There is a different way to write the definition without using  [by wf ...] (think about which argument you can use to do recursion on).
    You may try both definitions to see which one leads to simpler proofs. *)

Equations remove_last {A} {n : nat} (v : vec A (S n)) : vec A n :=
remove_last _ := todo.

(** Exercise, 3 star. Prove Lemma [remove_last_tail]. *)

Lemma remove_last_tail {A n} (v : vec A (S (S n))) : remove_last (tail v) = tail (remove_last v).
Proof.
Admitted.

(** Exercise, 3 star. Prove Lemma [remove_last_app1]. *)

Lemma remove_last_app1 {A n} (x : A) (v : vec A n) : remove_last (app1 v x) = v.
Proof.
Admitted.

(** We define a matrix [mtx] as a vector of vectors. *)

Definition mtx (A:Type) (m n : nat) : Type := vec (vec A n) m.

(** We think of [mtx A m n] as an m by n matrix. For example: *)

Definition mtx_test : mtx nat 2 3 := [[1; 2; 3];
                                      [4; 5; 6]].

(** Similarly, an [fmtx] is an fvector of fvectors. *)

Definition fmtx (A:Type) (m n : nat) : Type := fvec (fvec A n) m.

(** Exercise, 2 star: Finish the following definition of [mtx_to_fmtx].
    It should satisfy that [mtx_to_fmtx M i j] is the matrix entry at (i,j). *)

Definition mtx_to_fmtx {A m n} (M : mtx A m n) (i : fin m) (j : fin n) : A.
Admitted.

(** Exercise, 1 star: Test your definition of [mtx_to_fmtx] by finishing
    the examples [midx_0_0], [midx_0_1], [midx_1_1], [midx_1_2]. *)

Example midx_0_0 : mtx_to_fmtx mtx_test f0 f0 = 1.
Proof.
Admitted.

Example midx_0_1 : mtx_to_fmtx mtx_test f0 (fS f0) = 2.
Proof.
Admitted.

Example midx_1_1 : mtx_to_fmtx mtx_test (fS f0) (fS f0) = 5.
Proof.
Admitted.

Example midx_1_2 : mtx_to_fmtx mtx_test (fS f0) (fS (fS f0)) = 6.
Proof.
Admitted.

(** Notice that [@mtx_to_fmtx A m n] is a function
    from [mtx A m n] to [fmtx A m n]. *)

Check @mtx_to_fmtx : forall A m n, mtx A m n -> fmtx A m n.

(** Exercise, 3 star: Finish the definition of [fmtx_to_mtx], the inverse
    function of [mtx_to_fmtx], satisfying Lemmas [section_mtx_to_fmtx]
    and [retract_mtx_to_fmtx]. *)

Equations fmtx_to_mtx {A m n} (M : fmtx A m n) : mtx A m n :=
fmtx_to_mtx _ := todo.

(** Exercise, 3 star: Prove Lemma [section_mtx_to_fmtx]. *)

Lemma section_mtx_to_fmtx
  : forall {A m n} (M : mtx A m n), fmtx_to_mtx (mtx_to_fmtx M) = M.
Proof.
Admitted.

(** Exercise, 3 star: Prove Lemma [retract_mtx_to_fmtx']. *)

Lemma retract_mtx_to_fmtx'
  : forall {A m n} (M : fmtx A m n) (i : fin m),
      mtx_to_fmtx (fmtx_to_mtx M) i = M i.
Proof.
Admitted.

(** Exercise, 2 star: Prove Lemma [retract_mtx_to_fmtx]. *)

Lemma retract_mtx_to_fmtx
  : forall {A m n} (M : fmtx A m n),
      mtx_to_fmtx (fmtx_to_mtx M) = M.
Proof.
Admitted.

(** Exercise, 2 star: Finish definition [transpose_fmtx] to compute
    the transpose of an [fmtx]. *)

Definition transpose_fmtx {A m n} (M : fmtx A m n) : fmtx A n m.
Admitted.

(** Exercise, 2 star: Show that [transpose_fmtx] is correct by proving
    Lemma [transpose_fmtx_is_transpose]. *)

Lemma transpose_fmtx_is_transpose
  : forall {A m n} (M : fmtx A m n) (i : fin m) (j : fin n),
      transpose_fmtx M j i =  M i j.
Proof.
Admitted.

(** Exercise, 3 star: Define the transpose of an [mtx]. Consider the
    strong relationship [section_mtx_to_fmtx], [retract_mtx_to_fmtx]
    we have between [mtx] and [fmtx]. *)

(** Replace the Axiom [transpose_mtx] with your matrix transpose
    definition [transpose_mtx]. *)

Axiom transpose_mtx : forall {A m n}, mtx A m n -> mtx A n m.

(** Exercise, 3 star: Show that your [transpose_mtx] definition is
    correct by proving Lemma [transpose_mtx_is_transpose]. *)

Lemma transpose_mtx_is_transpose
  : forall {A m n} (M : mtx A m n) (i : fin m) (j : fin n),
      mtx_to_fmtx (transpose_mtx M) j i =  mtx_to_fmtx M i j.
Proof.
Admitted.

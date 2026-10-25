(** Monads

    Functional programs are nice, but sometimes we want effects.
    It turns out that many of these effects can be structured in a similar way,
    using so-called monads (a concept from category theory/ algebra).

    They are an abstract way of capturing many common programming concepts such as 
    * partiality, 
    * error handling, 
    * statefulness, 
    * non-determinism 
    * continuations 
    
    in a functional programming language. A monad consists of a type
    constructor 
    
      M : Type → Type 
    
    and two operations:
    • The reutrn (ret) operation takes a value [x : A] from a plain type and injects it into
      the monad. The value [ret x] has type [M A].
    • The bind operation takes a monadic value [m : M A] and applies a function
      [f : A → M B] to it. The resulting value bind [m f] has type [M B].*)

(** An important part of a monad is that it satisfies the monad laws: [ret] is a
    neutral element for [bind] and binding two functions consecutively is the same as
    binding one function that is composed using a [bind]. These laws are expressed
    by the following Coq definition that is parametrized by a type constructor [M] and
    the operations [ret] and [bind]: *)
(** The ret and bind functions have to satisfy the following monad laws:
      bind (ret x) f = f x
      bind m ret = m
      bind (bind m f ) g = bind m (λx.bind (f x) g) *)

Generalizable Variable A B.
Class Monad {M:Type -> Type} (ret: forall {A}, A -> M A)
      (bind: forall {A B}, M A -> ( A -> M B ) -> M B):=
  {bind_of_return : forall `(a:A) `(f:A -> M B),
          (bind (ret a) f) = (f a);
   return_of_bind : forall `(aM: M A), @bind _ A aM ret = aM;
   bind_assoc : forall {A B C : Type},
  forall `(aM: M A) `(f:A -> M B) (g:B -> M C),
    (bind (bind aM f) g) = (bind aM (fun a => bind (f a) g))}.


(* The purpose of these operations is best explained by an example. For that,
    we consider the option monad: *)


Require Import List EqNat.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Module Option.
Definition ret {A} ( x : A ) : option A := Some x .
Definition bind  {A B} ( m : option A ) ( f : A -> option B ) : option B :=
  match m with
  | Some x => f x
  | None => None
  end .

(** The option monad is used to model partiality: the constructor [Some] denotes
    that a computation has succeeded, and the constructor [None] denotes that a
    computation has failed. As shown in the above definition, [option_ret] models a
    successful computation, and [option_bind] propagates failures. *)

(** The [ret] and [bind] functions have to satisfy the following monad laws:
      bind (ret x) f = f x
      bind m ret = m
      bind (bind m f ) g = bind m (λx.bind (f x) g) *)

(** Recall the index function from the chapter “Poly” of Software Foundations
    that returns the nth element of a list, and yields [None] in case the element does
    not exist. We can use [option_bind] to use it multiple times, without having to
    perform explicit pattern matches on the results of index. *)
Fixpoint index { A } ( n : nat ) ( l : list A ) : option A :=
  match l with
  | nil => None
  | a :: l' =>
      if beq_nat n O then Some a else index ( pred n ) l'
  end.

Definition test ( l : list nat ) : option nat :=
  bind ( index 1 l ) ( fun n1 =>
  bind ( index 3 l ) ( fun n2 =>
  bind ( index 5 l ) ( fun n3 =>
    ret ( n1 + n2 + n3 ) ) ) ).

(** The function test retrieves the 1st, 3rd and 5th of the list [l] and sums these
    elements. If one of the elements does not exist, the whole function test fails by
    returning [None]. Let us try it out: *)

Eval compute in test [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]. (* Some 12 *)
Eval compute in test [1;2;3;4].  (* None *)
(** Exercise 1: Write 2 positive tests and 2 negative tests for multiple uses of
    [index] using [option_ret] and [option_bind] and prove these using the reflexivity
    tactic. *)
(* TODO: Exercise 1 *)

End Option.

(** Exercise 2: Prove that option satisfies the monad laws: *)

Local Instance OptionMonad: Monad ( @Option.ret ) ( @Option.bind ) . Admitted.

(** Another example is the list monad which can be used to deal with functions
    that yield multiple values. The ret function yields the singleton list, and bind
    applies a function to each element of the list and flattens the result. *)
Definition list_ret { A } ( x : A ) : list A := [ x ].
Fixpoint list_bind { A B } ( l : list A ) ( f : A -> list B ) : list B :=
  match l with
  | nil => nil
  | x :: l => f x ++ list_bind l f
  end.

(** Exercise 3: Implement a function that computes all permutations of a list: *)

(** For example permutations [1;2;3] may yield [[1;2;3]; [2;1;3]; [2;3;1];
    [1;3;2]; [3;1;2]; [3;2;1]] (it does not matter in which order the permuta-
    tions appear in the result). You should use list_ret and list_bind, and you
    may define at most one helper function using a Fixpoint. *)

(* Fixpoint permutations { A } ( l : list A ) : list ( list A ) := . *)
(* TODO: Exercise 3 *)
(* Hint: Try looking at permutations incrementally, how can we define the permutations
   based on those of a smaller list *)

(** Exercise 4: Prove that list satisfies the monad laws: *)
Local Instance list_monad : Monad ( @list_ret ) ( @list_bind ) . Admitted.
(* TODO: Exercise 4 *)

(** Yet another example is the state monad, which attaches state information to
    a type. Given a type [A], the corresponding type is a function that takes a state,
    and yields a resulting state and the return value of type [A]. The ret function
    produces a value without changing the state, and the bind function propagates
    changes to the state: *)
Definition state ( A : Type ) : Type := nat -> ( nat * A ) .

(** We have represented states using natural numbers, but one could of course
    use any type, or make the definition polymorphic in the type of states. For the
    purpose of this exercise, this will not be necessary. *)

(** Exercise 5: Implement the operations [state_ret] and [state_bind]. Prove that
    your operations satisfy the monad 
Local Instance state_monad : Monad ( @state_ret ) ( @state_bind ) . *)

(** In order to prove the above lemma, you need the functional extensionality axiom,
    which states that functions [f] and [g] are equal if [∀x . f x = g x]. It can 
    be obtained by adding the following to the beginning of your file: *)
Require Import FunctionalExtensionality.

Check @functional_extensionality. 
(* TODO: Exercise 5 *)  

(** We use the state monad to implement a function that relabels binary trees. 
    Binary trees are defined as: *)

Inductive tree :=
| leaf : tree
| node : tree -> nat -> tree -> tree.

(** The relabel function should preserve the tree structure, but change the labels
    such that they are numbed consecutively from left to right. For example:
    
             10                 1
           5   16   become    2   5         
          2 7                3 4
    
    
    In order to implement this function, we use the state monad to keep track of
    a counter. Each time we encounter a node, we increase the counter and relabel
    it. First we define a helper function to increase the counter. *)
    
(** Exercise 6: Write a function that produces the value of the state and in-
    creases the value of the state by one: *)
(* Definition state_inc : state nat := fill out *) 
(* TODO: Exercise 6 *)

(** Exercise 7: Write a function that relabels trees as described above
    You should use the monadic operations state_ret, state_bind and state_inc. *)
(* Fixpoint relabel ( t : tree ) : state tree := *)
(* TODO: Exercise 7 *)

(** Exercise 8: Write 2 tests of the relabel function and prove these using the
    reflexivity tactic. *)
(* TODO: Exercise 8 *)

(** Exercise 9: The size of a binary tree is defined as: *)
Fixpoint size ( t : tree ) : nat :=
  match t with
  | leaf => 0
  | node l x r => S ( size l + size r )
  end.
(** Write a lemma that states that the relabel function preserves the size of a
    binary tree and prove this lemma. *)
(* TODO: Exercise 9 *)

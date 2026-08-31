(** Monads

This is in preparation to the QuickChick chapter in book 4. 
There's also a short bit about Monads in:
https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html


Functional programs are nice, but sometimes we want effects, for example I/O.
It turns out that many of these effects can be structured in a similar way,
using so-called monads (a concept from category theory/ algebra).





They are an abstract way of capturing many common programming concepts such as 
* partiality, 
* error handling, 
* state, 
* non-determinism 
* continuations 

in a functional programming language. 


A monad consists of a type constructor 

M : Type → Type 

and two operations:
• The ret operation takes a value x : A from a plain type and injects it into
the monad. The value ret x has type M A.
• The bind operation takes a monadic value m : M A and applies a function
f : A → M B to it. The resulting value bind m f has type M B.*)








(** An important part of a monad is that it satisfies the monad laws: [ret] is a
    neutral element for [bind] and binding two functions consecutively is the same as
    binding one function that is composed using a [bind]. These laws are expressed
    by the following Coq definition that is parametrized by a type constructor [M] and
    the operations [ret] and [bind]: *)

(** In equations:
      bind (ret x) f = f x 
      bind m ret = m
      bind (bind m f ) g = bind m (λx.bind (f x) g) *)

Generalizable Variable A B.
Class Monad (M : Type -> Type) : Type :=
{ ret : forall {t : Type}, t -> M t
; bind : forall {t u : Type}, M t -> (t -> M u) -> M u
}.

Generalizable Variable M.
Class MonadLaws `(Monad M)
      :=
  {bind_of_return : forall `(a:A) `(f:A -> M B),
          (bind (ret a) f) = (f a);
   return_of_bind : forall `(aM: M A), bind aM ret = aM;
   bind_assoc : forall {A B C : Type},
  forall `(aM: M A) `(f:A -> M B) (g:B -> M C),
    (bind (bind aM f) g) = (bind aM (fun a => bind (f a) g))}.

(* Notice the use of type classes! 
   We could have packaged ret and bind in the record instead of having them as parameters. *)


   


(* The purpose of these operations is best explained by an example. 
   For that, we consider the option monad: *)

Require Import List EqNat.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Module Option. 
Print option. Locate option. (* from the stdlib. *)
Definition ret { A } : A -> option A := Some.
Definition bind { A B }( m : option A ) ( f : A -> option B ) : option B :=
match m with
| Some x => f x
| None => None
end.

Local Instance OptionMonad: Monad option:=
{| monad.ret := fun  t : Type => ret; monad.bind := fun  t u : Type =>  bind |}.

(** The option monad is used to model partiality: the constructor Some denotes
that a computation has succeeded, and the constructor None denotes that a
computation has failed. As shown in the above definition, ret models a
successful computation, and bind propagates failures. 
We have seen the Option type constructor before.
*)

(** The ret and bind functions have to satisfy the following monad laws:
  bind (ret x) f = f x 
  bind m ret = m
  bind (bind m f ) g = bind m (λx.bind (f x) g) *)

Local Instance OptionMonadLaws: @MonadLaws _ OptionMonad. Admitted.




(** Recall the index function from the chapter “Poly” of Software Foundations
that returns the nth element of a list, and yields None in case the element does
not exist. We can use option_bind to use it multiple times, without having to
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

(* This looks better with do-notation.*)                
Notation "c >>= f" := (bind c f) (at level 50, left associativity).
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
                    (at level 61, c1 at next level, right associativity).
                
Print test.


(** The function test retrieves the 1st, 3rd and 5th of the list l and sums these
elements. If one of the elements does not exist, the whole function test fails by
returning None. Let us try it out: *)

Eval compute in test [1 ;2 ; 3; 4 ;5 ;6 ; 7; 8 ;9 ;10]. 
Eval compute in test [1;2;3;4].  
(** Exercise 1 Write 2 positive tests and 2 negative tests for multiple uses of
index using ret and bind and prove these using the reflexivity
tactic. *)
End Option.







(** Another example is the list monad which can be used to deal with functions
that yield multiple values. The ret function yields the singleton list, and bind
applies a function to each element of the list and flattens the result. *)
Definition list_ret { A } ( x : A ) : list A := [ x ].
Fixpoint list_bind { A B }
( l : list A ) ( f : A -> list B ) : list B :=
match l with
| nil => nil
| x :: l => f x ++ list_bind l f
end.

Notation "c >>= f" := (list_bind c f) (at level 50, left associativity).
Notation "x <- c1 ;; c2" := (list_bind c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity).

Local Instance ListMonad : Monad list:=
{| monad.ret := fun  t : Type => list_ret; monad.bind := fun  t u : Type =>  list_bind |}.


Local Instance ListMonadLaws : MonadLaws ListMonad. Admitted.

(** Exercise 3 Implement a function that computes all permutations of a list:
Fixpoint permutations { A } ( l : list A ) : list ( list A ) := . *)













(** State *)
Module State.
(** Yet another example is the state monad, which attaches state information to
a type. Given a type A, the corresponding type is a function that takes a state,
and yields a resulting state and the return value of type A. The ret function
produces a value without changing the state, and the bind function propagates
changes to the state: *)
Definition state S A : Type := S -> ( S * A ).

(** The idea is that a stateful function A * nat -> nat * B  is the
    same as a monadic function A -> (nat -> (nat * B)) 
    Using Currying.    *)

(** We have represented states using natural numbers, but one could of
use any type, or make the definition polymorphic in the type of states. For the
purpose of this exercise, this will not be necessary. *)

(** Exercise 5 Implement the operations state_ret and state_bind. Prove that
your operations satisfy the monad laws: *)

Axiom todo : forall {A}, A.

(* Some, [_], 
   A -> (S-> (S * A)) *)

Definition state_ret { A } S ( x : A ) : state S A := fun s: S => (s, x).
Definition state_bind { A B } S ( aa : state S A ) ( ff : A -> state S B ) : state S B :=
fun s: S => let (sa,a) := (aa s) in ((ff a) sa).

(** In order to prove the above lemma, you need the functional extensionality axiom,
which states that functions f and g are equal if ∀x . f x = g x. It can be obtained
by adding the following to the beginning of your file: *)
Require Import FunctionalExtensionality.

Check @functional_extensionality. 

Local Instance StateMonad (S:Type): Monad (state S) := 
{| monad.ret := fun  t : Type => state_ret S; monad.bind := fun  t u : Type =>  state_bind S|}.

Local Instance StateMonadLaws (S:Type): MonadLaws (StateMonad S). Admitted.

(** We use the state monad to implement a function that relabels binary trees. Binary trees are defined as: 
Aside: like lists, trees define a monad. *)

Inductive tree :=
| leaf : tree
| node : tree -> nat -> tree -> tree.

(** The relabel function should preserve the tree structure, but change the labels
such that they are numbed consecutively from left to right. 
In order to implement this function, we use the state monad to keep track of
a counter. Each time we encounter a node, we increase the counter and relabel
it. First we define a helper function to increase the counter. *)

(** Exercise 6 
Write a function that produces the value of the state and increases the value of the state by one: 
Definition state_inc : state nat := fill out *) 

(** Exercise 7 Write a function that relabels trees as described above:
Fixpoint relabel ( t : tree ) : state tree := 
You should use the monadic operations state_ret, state_bind and state_inc. *)

(** Exercise 8 Write 2 tests of the relabel function and prove these using the
reflexivity tactic. *)

(** Exercise 9 The size of a binary tree is defined as: *)
Fixpoint size ( t : tree ) : nat :=
match t with
| leaf => 0
| node l x r => S ( size l + size r )
end.
(** Write a lemma that states that the relabel function preserves the size of a
    binary tree and prove this lemma. *)
End State.



    
(** Other monads *)

(* We can use the do-notation. 
   Reminiscent of imperative programming. *)

(** Error *)
Require Import String.
Module Error.
Notation E:=string.
Definition Error X:=(X+E)%type.
Definition ret {X}:=@inl X E.
(* If an error was raised stop the computation, 
   and just report the error. *)
Definition bind {A B:Type} ( m : Error A ) ( f : A -> Error B ) :=
  match m with
      inl x => f x 
    | inr e => inr e
  end.

Local Instance ErrorMonad: Monad Error := 
  {| monad.ret := fun  t : Type => ret ; monad.bind := fun  t u : Type =>  bind|}.
  
Local Instance ErrorMonadLaws : MonadLaws ErrorMonad. Admitted.
  
Notation "c >>= f" := (bind c f) (at level 50, left associativity).
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
    (at level 61, c1 at next level, right associativity).

Open Scope string.
(* A subtraction function with an error *)
Definition sub (n m:nat): Error nat:=
  match Compare_dec.le_lt_dec n m with
     right _ => inl (n - m)
  |  left _ => inr ("the RHS is too big")
  end.

Eval compute in (sub 2 5).

(* The numbers [1...n] *) Print nat.
Definition safe_seq (n:nat): Error (list nat):=
  match n with
    O => inr ("We want a non-empty list")%string
 |  S n => inl (seq 1 (S n)) end.



 
Eval compute in (inr "problem"%string >>= safe_seq).
Eval compute in (l<- safe_seq 0 ;; ret l).
Eval compute in (seq 1 2).
Eval compute in
    (l<- safe_seq 2 ;; ret ((map S) l)).

Definition hd : list nat-> Error (list nat).
intros [| h t].
exact (inr "list is empty"%string).
exact (inl [h]).
Show Proof.
Defined.


Check (safe_seq 4).
Eval compute in (l<-safe_seq 4 ;; (hd l)).
Eval compute in (l<-safe_seq 4 ;;
                  k<- (hd l) ;;
                 hd k).
Eval compute in (safe_seq 4 >>= hd >>= hd).
Eval compute in (safe_seq 4 >>= hd ).
End Error.

(** Reader *)
Module Reader.
(** An environment: *)
Variable E:Type.
Definition reader T := E -> T.
Definition ret {X}:X-> reader X := fun x => fun e => x.
Definition bind {A B} (m : reader A) (f : A -> reader B): reader B:=
  fun e => f (m e) e.

(**  The bound value and the function get access to the same shared environment for the computation.

Note: These definitions coincide with the definitions of the K and S combinators in the SKI-calculus. *)
Local Instance ReaderMonad : Monad reader := 
{| monad.ret := fun  t : Type => ret ; monad.bind := fun  t u : Type =>  bind |}.

Local Instance ReaderMonadLaws : MonadLaws ReaderMonad. Admitted.

End Reader.

(** Continuation Passing style
    CPS is one of the compiler optimization passes. *)

Module CPS.
Variable S:Type.
Definition M X:= (X->S)->S.
Definition ret {X}: X -> M X := fun x => (fun f => (f x)).
Definition bind {A B} (m : M A) (f : A -> M B): M B:=
  fun g =>  m (fun a : A => f a g).

  Local Instance CPSMonad : Monad M := 
  {| monad.ret := fun  t : Type => ret ; monad.bind := fun  t u : Type =>  bind |}.
  
  Local Instance CPSMonadLaws : MonadLaws CPSMonad. Admitted.
  

(** ret: we have a value and wait to receive a computation takes this value.
    bind: given a value and some function f, we compose the computation of f
    with the rest of the computation given in g 
    and then apply it to the starting value x. *)
End CPS.
(** Exercise (optional) prove that these satisfy the monad laws. *)
(* Will you need funext ? *)

(** We have seen many examples of monads:
    * partiality, 
    * error handling, 
    * statefulness, 
    * non-determinism 
    * continuations
    * reader
    * list  *)




(* Why is it useful to observe that all these effects are monads?
   Because there are general constructions. 
   Borrowing some code from extlib: *)
 Definition liftM
    {m : Type -> Type}
    {M : Monad m}
    {T U : Type} (f : T -> U) : m T -> m U :=
fun x => bind x (fun x => ret (f x)).

Definition apM {m : Type -> Type}
               {M : Monad m}
               {A B : Type} (fM:m (A -> B)) (aM:m A) : m B :=
bind fM (fun f => liftM f aM).

(* Left-to-right composition of Kleisli arrows. *)
Definition mcompose {m:Type->Type} {M: Monad m}
                    {T U V:Type}
                    (f: T -> m U) (g: U -> m V): (T -> m V) :=
                    fun x => bind (f x) g.

Definition join {m : Type -> Type} {a} `{Monad m} : m (m a) -> m a :=
                fun x => bind x (fun y => y).

(* Alternatively, one can use ret, lift and join in the definition of a monad.
This requires 7 laws. One can then define bind and derive our monad laws. *)

Module MonadBaseNotation.

  Delimit Scope monad_scope with monad.

  Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 61, right associativity) : monad_scope.
  Notation "f >=> g" := (@mcompose _ _ _ _ _ f g) (at level 61, right associativity) : monad_scope.
  Notation "e1 ;; e2" := (@bind _ _ _ _ e1%monad (fun _ => e2%monad))%monad
    (at level 61, right associativity) : monad_scope.

End MonadBaseNotation.



(** Next week we will see the probability monad *)

(* Here is a Coq library used for verifying haskell programs.
   Monads are an important part of it.
   These monads extract to monads in haskell, where the monadic programs can be run. *)
(* https://github.com/jwiegley/coq-haskell 
   https://github.com/coq-community/coq-ext-lib/blob/master/theories/Structures/Monad.v
*)

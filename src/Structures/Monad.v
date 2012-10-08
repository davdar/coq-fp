Require Import Data.Function.
Require Import Structures.Eqv.

Import EqvNotation.
Import FunctionNotation.

Class Monad m :=
{ ret : forall {A}, A -> m A
; bind : forall {A B}, m A -> (A -> m B) -> m B
}.

Definition rev_bind {m} {M:Monad m} {A B} (f:A -> m B) c := bind c f.

Module MonadNotation.
  Infix ">>=" := bind (at level 50, left associativity).
  Infix "=<<" := rev_bind (at level 51, right associativity).

  Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity).

  Notation "e1 ;; e2" := (_ <- e1 ;; e2)
    (at level 100, right associativity).
End MonadNotation.
Import MonadNotation.

Section Monad.
  Context {m} {M:Monad m}.

  Definition liftM {A B} (f:A -> B) (aM:m A) : m B := aM >>= (ret <.> f).
End Monad.

Class MonadLaws m {E:forall A {AE:Eqv A}, Eqv (m A)} {M:Monad m} :=
{ monad_bind_of_ret
    : forall {A B} {AE:Eqv A} {BE:Eqv B} {a:A} {f:A -> m B},
        ret a >>= f ~= f a
; monad_ret_of_bind
    : forall {A} {AE:Eqv A} {c:m A},
        c >>= ret ~= c
; monad_associativity
    : forall {A B C} {AE:Eqv A} {BE:Eqv B} {CE:Eqv C}
             {c:m A} {f:A -> m B} {g:B -> m C},
        (c >>= f) >>= g ~= c >>= (fun x => f x >>= g)
}.
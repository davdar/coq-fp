Require Import Data.FunctionPre.

Require Import Structures.Eqv.
Require Import Structures.Functor.
Require Import Structures.Applicative.
Require Import Structures.Injection.

Import EqvNotation.
Import FunctionNotation.

Class Monad m :=
  { ret : forall {A}, A -> m A
  ; bind : forall {A B}, m A -> (A -> m B) -> m B
  }.
Local Infix ">>=" := bind (at level 50, left associativity).

Definition revbind {m} {M:Monad m} {A B} : (A -> m B) -> m A ->  m B := flip bind.

Definition kleisli_compose {m} {M:Monad m} {A B C}
    (g:B -> m C) (f:A -> m B) (a:A) : m C :=
  f a >>= g.

Definition kleisli_revcompose {m} {M:Monad m} {A B C}
    : (A -> m B) -> (B -> m C) -> A -> m C :=
  flip kleisli_compose.

Module MonadNotation.
  Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity).

  Notation "e1 ;; e2" := (_ <- e1 ;; e2)
    (at level 100, right associativity).

  Infix ">>=" := bind (at level 50, left associativity).
  Infix "=<<" := revbind (at level 51, right associativity).
  Infix "<=<" := kleisli_compose (at level 53, right associativity).
  Infix ">=>" := kleisli_revcompose (at level 53, right associativity).
End MonadNotation.
Import MonadNotation.

Definition join {m} {M:Monad m} {A} : m (m A) -> m A := revbind id.
Definition mmap {m} {M:Monad m} {A B} : (A -> B) -> m A -> m B :=
  revbind <.> compose ret.
Definition mapply {m} {M:Monad m} {A B} (fM:m (A -> B)) (aM:m A) : m B :=
  fM >>= flip mmap aM.

Instance Monad_Applicative {m} {M:Monad m} : Applicative m :=
  { fret _a := ret
  ; fapply _a _b := mapply
  }.

Definition iso_Monad {m} n {B:FunctorBijection m n} {nM:Monad n} : Monad m :=
  {| ret _A := ffrom <.> ret
   ; bind _A _B aM f := ffrom $ bind (fto aM) (fto <.> f)
  |}.

Class MonadLaws m {E:forall A {AE:Eqv A}, Eqv (m A)} {M:Monad m} :=
  { monad_bind_of_ret
      : forall {A B} {AE:Eqv A} {BE:Eqv B} {x:A} {f:A -> m B},
          ret x >>= f '~= f x
  ; monad_ret_of_bind
      : forall {A} {AE:Eqv A} {c:m A},
          c >>= ret '~= c
  ; monad_associativity
      : forall {A B c} {AE:Eqv A} {BE:Eqv B} {CE:Eqv c}
               {aM:m A} {f:A -> m B} {g:B -> m c},
          aM >>= f >>= g '~= aM >>= fun x => f x >>= g
  }.

Fixpoint replicateM {m A} {M:Monad m} (n:nat) (aM:m A) : m (list A) :=
  match n with
  | O => ret nil
  | S n' =>
      x <- aM ;;
      xs <- replicateM n' aM ;;
      ret $ cons x xs
  end.

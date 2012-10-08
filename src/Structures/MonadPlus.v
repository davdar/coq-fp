Require Import Data.Function.
Require Import Data.Sum.
Require Import Structures.Monad.
Require Import Structures.Monoid.
Require Import Structures.Pointed.

Import FunctionNotation.

Class MonadPlus m :=
  { monad_plus_Pointed :> forall {A}, Pointed (m A)
  ; mplus : forall {A B}, m A -> m B -> m (A+B)
  }.

Module MonadPlusNotation.
  Infix "<+>" := mplus (at level 45, right associativity).
End MonadPlusNotation.

Instance MonadPlus_Monoid m {M:Monad m} {MP:MonadPlus m} : forall A, Monoid (m A) :=
  { monoid_times := liftM collapse <..> mplus }.

Section MonadPlus.
  Context {m} {M:Monad m} {MP:MonadPlus m}.

  Definition msum {A} : list (m A) -> m A := monoid_product.
End MonadPlus.

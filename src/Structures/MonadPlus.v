Require Import Data.Function.
Require Import Structures.Monad.
Require Import Structures.Monoid.
Require Import Structures.Alternative.
Require Import Structures.Injection.
Require Import Structures.Additive.

Import FunctionNotation.
Import AdditiveNotation.

Local Infix "+" := sum.

Class MonadPlus m :=
  { mzero : forall {A}, m A
  ; mplus : forall {A B}, m A -> m B -> m (A+B)
  }.

Instance MonadPlus_Alternative m {MP:MonadPlus m} : Alternative m :=
  { fzero := @mzero _ _
  ; fplus := @mplus _ _ 
  }.

Section iso_MonadPlus.
  Variable (n:Type -> Type).
  Context {m} {B:FunctorBijection m n} {nMP:MonadPlus n}.

  Definition iso_MonadPlus_mzero {A} : m A := ffrom mzero.
  Definition iso_MonadPlus_mplus {A B} (aM:m A) (bM:m B) : m (A+B) :=
    ffrom $ mplus (fto aM) (fto bM).
  Definition iso_MonadPlus : MonadPlus m :=
    {| mzero := @iso_MonadPlus_mzero
     ; mplus := @iso_MonadPlus_mplus
    |}.
End iso_MonadPlus.

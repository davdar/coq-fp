Require Import Data.Prod.
Require Import Data.Function.
Require Import Structures.Monad.
Require Import Structures.Monoid.
Require Import Structures.Functor.
Require Import Structures.Multiplicative.
Require Import Data.Type.

Import MultiplicativeNotation.

Class MonadWriter W {WM:Monoid W} (m:Type -> Type) :=
  { tell : W -> m unit
  ; listen : forall {A}, m A -> m (A*W)
  ; pass : forall {A}, m (A*(W -> W)) -> m A
  }.

Definition censor {W A m} {M:Monad m} {wM:Monoid W} {MW:MonadWriter W m}
    (f:W -> W) (aM:m A) : m A :=
  pass (fmap (fun a => (a,f)) aM).

Definition restart {W A m} {M:Monad m} {wM:Monoid W} {MW:MonadWriter W m}
    : m A -> m A :=
  censor (const gunit).

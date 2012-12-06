Require Import FP.Data.Function.
Require Import FP.Structures.Injection.

Import FunctionNotation.

Class MonadReader R m :=
  { ask : m R
  ; local : forall {A}, (R -> R) -> m A -> m A
  }.

Section iso_MonadReader.
  Variable n:Type -> Type.
  Context {m} {B:FunctorBijection m n} {R} {nMR:MonadReader R n}.

  Definition iso_MonadReader_ask : m R := ffrom ask.
  Definition iso_MonadReader_local {A} (f:R -> R) : m A -> m A :=
    ffrom '.' local f '.' fto.
  Definition iso_MonadReader : MonadReader R m :=
    {| ask := iso_MonadReader_ask
     ; local := @iso_MonadReader_local
    |}.
End iso_MonadReader.
Require Import Data.FunctionPre.

Require Import Structures.Injection.

Import FunctionNotation.

Class MonadReader R m :=
{ ask : m R
; local : forall {A}, (R -> R) -> m A -> m A
}.

Section iso_MonadReader.
  Context {m} {n} {B:FunctorBijection m n} {R} {nMP:MonadReader R n}.
  Definition iso_MonadReader_ask : m R := ffrom ask.
  Definition iso_MonadPlus_local {A} (f:R -> R) : m A -> m A := ffrom <.> local f <.> fto.
End iso_MonadReader.
Definition iso_MonadReader {m} n {B:FunctorBijection m n} {R} {nMR:MonadReader R n} : MonadReader R m :=
  {| ask := @iso_MonadReader_ask _ _ _ _ _
   ; local := @iso_MonadPlus_local _ _ _ _ _
  |}.
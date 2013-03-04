Require Import FP.Structures.Injection.
Require Import FP.Data.Function.

Import FunctionNotation.

Class MReader (R:Type) (m:Type->Type) : Type :=
  { ask : m R
  ; local : forall {A}, (R -> R) -> m A -> m A
  }.

Section DerivingMReader.
  Variable (n:Type -> Type).
  Context {m} {HFB_:HasFunctorBijection m n} {R} {MReader_:MReader R n}.

  Definition DerivingMReader_ask : m R := ffrom ask.
  Definition DerivingMReader_local {A} (f:R -> R) : m A -> m A :=
    ffrom '.' local f '.' fto.
  Definition DerivingMReader : MReader R m :=
    {| ask := DerivingMReader_ask
     ; local := @DerivingMReader_local
    |}.
End DerivingMReader.

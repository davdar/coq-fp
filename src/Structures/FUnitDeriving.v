Require Import FP.Structures.Injection.
Require Import FP.Structures.FUnit.
Require Import FP.Data.Function.

Import FunctionNotation.

Section Deriving_FUnit.
  Context {m:Type->Type}.
  Variable (n:Type->Type).
  Context {HFI_:HasFunctorInjection n m}.
  Context {FUnit_:FUnit n}.

  Definition deriving_funit {A} : A -> m A := finject '.' funit.

  Definition Deriving_FUnit : FUnit m :=
    {| funit := @deriving_funit |}.
End Deriving_FUnit.
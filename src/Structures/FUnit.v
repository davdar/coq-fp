Require Import FP.Structures.EqvRel.
Require Import FP.Relations.Setoid.

Import ProperNotation.

Class FUnit (t:Type->Type) :=
  { funit : forall {A}, A -> t A }.

Section FUnitWF.
  Context {t:Type -> Type}.
  Context {FUnit_:FUnit t}.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvWF_:EqvEnvWF}.
  Context {E_R_t:forall {A} {aER:PE_R A}, PE_R (t A)}.

  Class FUnitWF :=
    { funit_respect :>
        forall {A} {aER:PE_R A},
          Proper PE_eqv (funit (A:=A))
    }.
End FUnitWF.
Arguments FUnitWF t {_ _ _ _}.
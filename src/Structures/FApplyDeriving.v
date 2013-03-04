Require Import FP.Structures.FUnit.
Require Import FP.Structures.FApply.

Section FMap.
  Context {m} {FUnit_:FUnit m} {FApply_:FApply m}.
  Variable (EqvEnv_:EqvEnv).
  Context {RPromote:forall {A} {aER:EqvRel A}, EqvRel (m A)}.

  Definition FApply_Functor : FMap t :=
    {| fmap := @fapply_fmap |}.
  Definition FApply_FTimes : FTimes t :=
    {| ftimes := @fapply_ftimes |}.
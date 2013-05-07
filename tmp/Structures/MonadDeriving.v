Require Import FP.Structures.FUnit.
Require Import FP.Data.Function.
Require Import FP.Data.FunctionStructures.
Require Import FP.Structures.Category.
Require Import FP.Structures.Proxy.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Applicative.
Require Import FP.Structures.Related.
Require Import FP.Structures.Functor.
Require Import FP.Structures.EqvEnv.
Require Import FP.Structures.Monad.
Require Import FP.Relations.Setoid.

Import ProperNotation.
Import FunctionNotation.

Section Deriving_MBind.
  Context {m:Type->Type}.
  Variable (n:Type->Type).
  Context {nm_HasFunctorBijection:HasFunctorBijection n m}.
  Context {n_MBind:MBind n}.

  Definition deriving_bind {A B} (aM:m A) (f:A -> m B) : m B :=
    ffrom $ bind (fto aM) (fto '.' f).

  Definition Deriving_MBind : MBind m :=
    {| bind := @deriving_bind |}.
End Deriving_MBind.

Section Deriving_FMap_Monad.
  Context {m:Type -> Type} {FUnit_:FUnit m} {MBind_:MBind m}.
  Definition deriving_FMap_Monad {A} {B} : (A -> B) -> m A -> m B := bind_fmap.
  Definition Deriving_FMap_Monad : FMap m :=
    {| fmap := @deriving_FMap_Monad |}.
End Deriving_FMap_Monad.

Section Deriving_FApply_FBind.
  Context {m:Type -> Type} {FUnit_:FUnit m} {MBind_:MBind m}.
  Definition deriving_FApply_MBind {A} {B} : m (A -> B) -> m A -> m B := bind_fapply.
  Definition Deriving_FApply_MBind : FApply m :=
    {| fapply := @deriving_FApply_MBind |}.
End Deriving_FApply_FBind.

Section Deriving_ApplicativeWF_MonadWF.
  Context {m:Type -> Type}.
  Context {FUnit_:FUnit m} {FApply_:FApply m} {MBind_:MBind m}.

  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {mPER:forall {A} {aPER:Px (env_PER A)}, Px (env_PER (m A))}.
  Context {mPER':forall {A} {aPER:Px (env_PER A)} {aPER':Px (env_PER_WF A)},
                   Px (env_PER_WF (m A))}.

  Context {FUnitWF_:FUnitWF m}.
  Context {MonadWF_:MonadWF m}.

  Global Instance bind_fapply_respect
      {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
      {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)} :
    Proper env_eqv (bind_fapply (A:=A) (B:=B)).
  Proof.
    unfold bind_fapply ; logical_eqv.
  Qed.

  Class MonadRespApplicative :=
    { bind_respect_fapply :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}
          (fM:m (A -> B)) {fP:Proper env_eqv fM}
          (aM:m A) {aMP:Proper env_eqv aM},
            env_eqv
            (fapply fM aM)
            (bind_fapply fM aM)
    }.

  Context {MonadRespApplicative_:MonadRespApplicative}.

  Local Instance fapply_respect'
      {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
      {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)} :
    Proper env_eqv (fapply (A:=A) (B:=B)).
  Proof.
    logical_eqv_intro.
    repeat rewrite bind_respect_fapply ; logical_eqv.
  Qed.
  Hint Extern 9 (Proper env_eqv fapply) =>
    apply fapply_respect' : typeclass_instances.

  Definition Deriving_ApplicativeWF_MonadWF : ApplicativeWF m.
  Proof.
    constructor ; intros.
    - rewrite bind_respect_fapply ; logical_eqv ; simpl.
      rewrite bind_left_unit ; logical_eqv ; simpl.
      apply bind_right_unit ; auto.
    - rewrite bind_respect_fapply ; logical_eqv.
      rewrite bind_respect_fapply ; logical_eqv.
      rewrite bind_respect_fapply ; logical_eqv.
      rewrite bind_respect_fapply ; logical_eqv.
      rewrite bind_respect_fapply ; logical_eqv ; simpl.
      rewrite bind_associativity ; logical_eqv.
      rewrite bind_associativity ; logical_eqv.
      rewrite bind_left_unit ; logical_eqv.
      rewrite bind_associativity ; logical_eqv.
      rewrite bind_left_unit ; logical_eqv.
      rewrite bind_associativity ; logical_eqv.
      rewrite bind_associativity ; logical_eqv.
      rewrite bind_left_unit ; logical_eqv.
      rewrite bind_associativity ; logical_eqv.
      rewrite bind_left_unit ; logical_eqv ; simpl.
      logical_eqv.
    - rewrite bind_respect_fapply ; logical_eqv ; simpl.
      rewrite bind_left_unit ; logical_eqv.
      rewrite bind_left_unit ; logical_eqv.
    - rewrite bind_respect_fapply ; logical_eqv ; simpl.
      rewrite bind_respect_fapply ; logical_eqv ; simpl.
      rewrite bind_left_unit ; logical_eqv.
      rewrite bind_left_unit ; logical_eqv ; simpl.
      logical_eqv.
    - apply fapply_respect'.
  Qed.
End Deriving_ApplicativeWF_MonadWF.
Arguments MonadRespApplicative m {_ _ _ _ _ _}.
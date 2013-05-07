Require Import FP.Structures.EqvEnv.
Require Import FP.Structures.Proxy.
Require Import FP.Structures.Eqv.
Require Import FP.Relations.Setoid.

Import ProperNotation.

Class FUnit (t:Type->Type) :=
  { funit : forall {A}, A -> t A }.

Section FUnitWF.
  Context {t:Type -> Type}.
  Context {FUnit_:FUnit t}.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {E_R_t:forall {A} {aPE:Px (env_PER A)}, Px (env_PER (t A))}.
  Context {E_R_WF_t :
    forall {A} {aPE:Px (env_PER A)} {aPEWF:Px (env_PER_WF A)},
    Px (env_PER_WF (t A))}.

  Class FUnitWF :=
    { funit_respect :>
        forall {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)},
        Proper env_eqv (funit (A:=A))
    }.
End FUnitWF.
Arguments FUnitWF t {_ _ _ _}.
Hint Extern 9 (Proper env_eqv funit) => apply funit_respect : typeclass_instances.

Section EqvEnv_eqv.
  Local Instance EqvEnv_ : EqvEnv := eqv_EqvEnv.
  Local Instance EqvEnvLogical_ : EqvEnvLogical := eqv_EqvEnvLogical.
  Context {t:Type -> Type}.
  Context {FUnit_:FUnit t}.
  Context {E_R_t:forall {A} {aPE:Eqv A}, Eqv (t A)}.
  Context {E_R_WF_t :
    forall {A} {aPE:Eqv A} {aPEWF:Eqv_PE_WF A},
    Eqv_PE_WF (t A)}.
  Context {FUnitWF_:FUnitWF t}.

  Global Instance funit_respect_eqv :
    forall {A} {aER:Eqv A} {aER':Eqv_PE_WF A},
    Proper eqv (funit (A:=A)).
  Proof.
    intros.
    pose (@funit_respect _ _ _ _ _).
    eauto.
  Qed.
End EqvEnv_eqv.
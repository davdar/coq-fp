Require Import FP.Data.Function.
Require Import FP.Data.FunctionStructures.
Require Import FP.Structures.FUnit.
Require Import FP.Relations.Setoid.
Require Import FP.Structures.FMultiplicative.
Require Import FP.Structures.Related.
Require Import FP.Structures.Proxy.
Require Import FP.Structures.EqvEnv.
Require Import FP.Structures.Functor.

Import FunctionNotation.
Import ProperNotation.

Class FApply (t:Type->Type) :=
  { fapply : forall {A B}, t (A -> B) -> t A -> t B }.

Class Applicative (t:Type->Type) : Type :=
  { Applicative_FUnit : FUnit t
  ; Applicative_FApply : FApply t
  }.
Hint Resolve Build_Applicative : typeclass_instances.
Hint Immediate Applicative_FUnit : typeclass_instances.
Hint Immediate Applicative_FApply : typeclass_instances.

Section FApply.
  Context {t} {FUnit_:FUnit t} {FApply_:FApply t}.

  Definition fapply_fmap {A B} : (A -> B) -> t A -> t B :=
    fapply '.' funit.
  Definition fapply_ftimes {A B} (aT:t A) (bT:t B) : t (A*B) :=
    fapply (fapply (funit pair) aT) bT.
End FApply.
Arguments fapply_fmap {t FUnit_ FApply_ A B} _ _ / . 
Arguments fapply_ftimes {t FUnit_ FApply_ A B} _ _ / .

Module ApplicativeNotation.
  Infix "<@>" := fapply (at level 46, left associativity).
End ApplicativeNotation.

Section ApplicativeWF.
  Context {t:Type->Type}.
  Context {FUnit_:FUnit t} {FApply_:FApply t}.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {PE_R_t:forall {A} {aER:Px (env_PER A)}, Px (env_PER (t A))}.
  Context {PE_R_t' :
    forall {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)},
    Px (env_PER_WF (t A))}.

  Class ApplicativeWF :=
    { fapply_unit :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}
          (aT:t A) {aTP:Proper env_eqv aT},
            env_eqv
            (fapply (funit id) aT)
            aT
    ; fapply_composition :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}
          {C} {cER:Px (env_PER C)} {bER':Px (env_PER_WF C)}
          (fT:t (A -> B)) {fTP:Proper env_eqv fT}
          (gT:t (B -> C)) {gTP:Proper env_eqv gT}
          (aT:t A) {aTP:Proper env_eqv aT},
            env_eqv
            (fapply gT (fapply fT aT))
            (fapply (fapply (fapply (funit compose) gT) fT) aT)
    ; fapply_homomorphism :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}
          (f:A -> B) {fP:Proper env_eqv f}
          (a:A) {aP:Proper env_eqv a},
            env_eqv
            (fapply (funit f) (funit a))
            (funit (f a))
    (* is this derivable? necessary? *)
    ; fapply_interchange :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}
          (fT:t (A -> B)) {fTP:Proper env_eqv fT}
          (a:A) {aP:Proper env_eqv a},
            env_eqv
            (fapply fT (funit a))
            (fapply (funit (apply_to a)) fT)
    ; fapply_respect :>
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)},
            Proper env_eqv (fapply (A:=A) (B:=B))
    }.
End ApplicativeWF.
Arguments ApplicativeWF t {_ _ _ _ _}. 

Section Deriving_FMap_FApply.
  Context {t:Type -> Type} {FUnit_:FUnit t} {FApply_:FApply t}.
  Definition deriving_FMap_FApply {A} {B} : (A -> B) -> t A -> t B := fapply_fmap.
  Definition Deriving_FMap_FApply : FMap t :=
    {| fmap := @deriving_FMap_FApply |}.
End Deriving_FMap_FApply.

Section Deriving_FunctorWF_ApplicativeWF.
  Variable (t:Type -> Type).
  Context {FUnit_:FUnit t} {FApply_:FApply t}.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {PE_R_t:forall {A} {aER:Px (env_PER A)}, Px (env_PER (t A))}.
  Context {PE_R_t' :
    forall {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)},
    Px (env_PER_WF (t A))}.

  Context {FUnitWF_:FUnitWF t}.
  Context {ApplicativeWF_:ApplicativeWF t}.

  Context {FMap_:FMap t}.
  Class ApplicativeRespectsFunctor :=
    { fapply_respect_fmap :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}
          (f:A -> B) {fP:Proper env_eqv f}
          (aT:t A) {aTP:Proper env_eqv aT},
            env_eqv
            (fmap f aT)
            (fapply_fmap f aT)
    }.
  Context {ApplicativeRespectsFunctor_:ApplicativeRespectsFunctor}.

  Local Instance fapply_fmap_respect'
      {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
      {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)} :
    Proper env_eqv (fapply_fmap (A:=A) (B:=B)).
  Proof.
    unfold fapply_fmap ; logical_eqv.
  Qed.

  Local Instance fmap_respect'
      {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
      {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)} :
    Proper env_eqv (fmap (A:=A) (B:=B)).
  Proof.
    logical_eqv_intro.
    repeat rewrite fapply_respect_fmap ; logical_eqv.
  Qed.

  Definition Deriving_FunctorWF_ApplicativeWF : FunctorWF t.
  Proof.
    constructor ; intros ; simpl.
    - rewrite fapply_respect_fmap ; logical_eqv ; simpl.
      rewrite fapply_unit ; logical_eqv.
    - rewrite fapply_respect_fmap ; logical_eqv.
      rewrite fapply_respect_fmap ; logical_eqv .
      rewrite fapply_respect_fmap ; logical_eqv ; simpl.
      rewrite fapply_composition ; logical_eqv ; simpl.
      rewrite fapply_homomorphism ; logical_eqv.
      rewrite fapply_homomorphism ; logical_eqv.
    - apply fmap_respect'.
  Qed.
End Deriving_FunctorWF_ApplicativeWF.
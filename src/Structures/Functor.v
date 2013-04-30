Require Import FP.Data.Function.
Require Import FP.Structures.Proxy.
Require Import FP.Structures.EqvEnv.
Require Import FP.Relations.Setoid.

Import FunctionNotation.
Import ProperNotation.

Class FMap (t:Type->Type) : Type :=
  { fmap : forall {A B}, (A -> B) -> t A -> t B }.
Arguments fmap {t FMap A B} _ _ : simpl never.

Section FMap.
  Context {t u} {FMap_t:FMap t} {FMap_u:FMap u}.

  Definition fmap2 {A} {B} : (A -> B) -> u (t A) -> u (t B) := fmap '.' fmap.

  Context {v} {FMap_v:FMap v}.

  Definition fmap3 {A} {B} : (A -> B) -> v (u (t A)) -> v (u (t B)) := fmap '.' fmap2.
End FMap.

Module FunctorNotation.
  Infix "<$>" := fmap (at level 46, left associativity).
  Infix "<$$>" := fmap2 (at level 46, left associativity).
  Infix "<$$$>" := fmap3 (at level 46, left associativity).
End FunctorNotation.

Section FunctorWF.
  Variable (t:Type->Type).
  Context {FMap_:FMap t}.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {PE_R_t:forall {A} {aER:Px (env_PER A)}, Px (env_PER (t A))}.
  Context {PE_R_t' :
    forall {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)},
    Px (env_PER_WF (t A))}.
  
  Class FunctorWF :=
    { fmap_id :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          (f:A -> A) (fP:Proper env_eqv f)
          (aT:t A) (aTP:Proper env_eqv aT),
            env_eqv
            (fmap id aT)
            aT
    ; fmap_compose :
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}
          {C} {cER:Px (env_PER C)} {cER':Px (env_PER_WF C)}
          (f:A -> B) (fP:Proper env_eqv f)
          (g:B -> C) (gP:Proper env_eqv g)
          (aT:t A) (aTP:Proper env_eqv aT),
            env_eqv
            (fmap (g '.' f) aT)
            ((fmap g '.' fmap f) aT)
    ; fmap_respect :>
        forall
          {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}
          {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)},
            Proper env_eqv (fmap (A:=A) (B:=B))
    }.
End FunctorWF.
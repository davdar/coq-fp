Require Import FP.Data.Function.
Require Import FP.Structures.Proxy.
Require Import FP.Structures.EqvRel.
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
  Context {EqvEnvWF_:EqvEnvWF}.
  Context {PE_R_t:forall {A} {aER:PE_R A}, PE_R (t A)}.
  
  Class FunctorWF :=
    { fmap_id :
        forall
          {A} {aER:PE_R A}
          (f:A -> A) (fP:Proper PE_eqv f)
          (aT:t A) (aTP:Proper PE_eqv aT),
            PE_eqv
            (fmap id aT)
            aT
    ; fmap_compose :
        forall
          {A} {aER:PE_R A}
          {B} {bER:PE_R B}
          {C} {cER:PE_R C}
          (f:A -> B) (fP:Proper PE_eqv f)
          (g:B -> C) (gP:Proper PE_eqv g)
          (aT:t A) (aTP:Proper PE_eqv aT),
            PE_eqv
            (fmap (g '.' f) aT)
            ((fmap g '.' fmap f) aT)
    ; fmap_respect :>
        forall
          {A} {aER:PE_R A}
          {B} {bER:PE_R B},
            Proper PE_eqv (fmap (A:=A) (B:=B))
    }.
End FunctorWF.
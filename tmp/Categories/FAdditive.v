Require Import FP.Data.Sum.
Require Import FP.Data.Type.
Require Import FP.Structures.FUnit.
Require Import FP.Structures.Functor.
Require Import FP.Structures.EqvRel.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.FZero.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Proxy.
Require Import FP.Relations.Setoid.

Import FunctionNotation.
Import AdditiveNotation.

Class FPlus (t:Type->Type) :=
  { fplus : forall {A B}, t A -> t B -> t (A+B) }.

Class FAdditive (t:Type -> Type) : Type :=
  { FAdditive_FZero : FZero t
  ; FAdditive_FPlus : FPlus t
  }.
Hint Resolve Build_FAdditive : typeclass_instances.
Hint Immediate FAdditive_FZero : typeclass_instances.
Hint Immediate FAdditive_FPlus : typeclass_instances.

Module FAdditiveNotation.
  Infix "<+>" := fplus (at level 48, left associativity).
End FAdditiveNotation.


Section FAdditiveWF.
  Context {t:Type->Type}.
  Context {FMap_:FMap t} {FPlus_:FPlus t}.
  Context {EqvEnv_:EqvEnv}.
  Context {RPromote:forall {A} {aER:EqvRel A}, EqvRel (t A)}.
  Context {RPromote_sum:forall {A} {aER:EqvRel A} {B} {bER:EqvRel B}, EqvRel (A+B)}.

  Class FAdditiveWF :=
    { fplus_left_zero :
        forall
          {A} {aER:EqvRel A}
          {B} {bER:EqvRel B}
          (bT:t B) (bT':t B) {bTP:env_R bT bT'},
            env_R
            (fplus fzero bT)
            (fmap inr bT')
    ; fplus_right_zero :
        forall
          {A} {aER:EqvRel A}
          {B} {bER:EqvRel B}
          (aT:t A) (aT':t A) {aTP:env_R aT aT'},
            env_R
            (fplus aT fzero)
            (fmap inl aT)
    ; fplus_associativity :
        forall
          {A} {aER:EqvRel A}
          {B} {bER:EqvRel B}
          {C} {cER:EqvRel C}
          (aT:t A) (bT:t B) (cT:t C),
            env_R
            (fplus (fplus aT bT) cT)
            (fmap sum_associate (fplus aT (fplus bT cT)))
    }.
       
End FAdditiveWF.

Section Deriving_FAdditive
  Variable (n:Type -> Type).
  Context {m} {B:HasFunctorBijection m n} {nMP:MonadPlus n}.

  Definition iso_MonadPlus_mzero {A} : m A := ffrom mzero.
  Definition iso_MonadPlus_mplus {A B} (aM:m A) (bM:m B) : m (A+B) :=
    ffrom $ mplus (fto aM) (fto bM).
  Definition iso_MonadPlus : MonadPlus m :=
    {| mzero := @iso_MonadPlus_mzero
     ; mplus := @iso_MonadPlus_mplus
    |}.
End Deriving_FAdditive.
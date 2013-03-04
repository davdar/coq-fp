Require Import FP.Data.Function.
Require Import FP.Data.FunctionStructures.
Require Import FP.Structures.FUnit.
Require Import FP.Relations.Setoid.
Require Import FP.Structures.FMultiplicative.
Require Import FP.Structures.Related.
Require Import FP.Structures.EqvRel.
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
  Context {EqvEnvWF_:EqvEnvWF}.
  Context {PE_R_t:forall {A} {aER:PE_R A}, PE_R (t A)}.

  Class ApplicativeWF :=
    { fapply_unit :
        forall
          {A} {aER:PE_R A}
          {B} {bER:PE_R B}
          (aT:t A) {aTP:Proper PE_eqv aT},
            PE_eqv
            (fapply (funit id) aT)
            aT
    ; fapply_composition :
        forall
          {A} {aER:PE_R A}
          {B} {bER:PE_R B}
          {C} {cER:PE_R C}
          (fT:t (A -> B)) {fTP:Proper PE_eqv fT}
          (gT:t (B -> C)) {gTP:Proper PE_eqv gT}
          (aT:t A) {aTP:Proper PE_eqv aT},
            PE_eqv
            (fapply gT (fapply fT aT))
            (fapply (fapply (fapply (funit compose) gT) fT) aT)
    ; fapply_homomorphism :
        forall
          {A} {aER:PE_R A}
          {B} {bER:PE_R B}
          (f:A -> B) {fP:Proper PE_eqv f}
          (a:A) {aP:Proper PE_eqv a},
            PE_eqv
            (fapply (funit f) (funit a))
            (funit (f a))
    (* is this derivable? *)
    ; fapply_interchange :
        forall
          {A} {aER:PE_R A}
          {B} {bER:PE_R B}
          (fT:t (A -> B)) {fTP:Proper PE_eqv fT}
          (a:A) {aP:Proper PE_eqv a},
            PE_eqv
            (fapply fT (funit a))
            (fapply (funit (apply_to a)) fT)
    ; fapply_respect :>
        forall
          {A} {aER:PE_R A}
          {B} {bER:PE_R B},
            Proper PE_eqv (fapply (A:=A) (B:=B))
    }.
End ApplicativeWF.
Arguments ApplicativeWF t {_ _ _ _ _}. 
Hint Resolve fapply_respect : logical_eqv_db.

Section Deriving_FunctorWF_ApplicativeWF.
  Variable (t:Type -> Type).
  Context {FUnit_:FUnit t} {FApply_:FApply t}.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvWF_:EqvEnvWF}.
  Context {PE_R_t:forall {A} {aER:PE_R A}, PE_R (t A)}.

  Context {FUnitWF_:FUnitWF t}.
  Context {ApplicativeWF_:ApplicativeWF t}.

  Context {FMap_:FMap t}.
  Class ApplicativeRespectsFunctor :=
    { fapply_respect_fmap :
        forall
          {A} {aER:PE_R A}
          {B} {bER:PE_R B}
          (f:A -> B) {fP:Proper PE_eqv f}
          (aT:t A) {aTP:Proper PE_eqv aT},
            PE_eqv
            (fmap f aT)
            (fapply_fmap f aT)
    }.
  Context {ApplicativeRespectsFunctor_:ApplicativeRespectsFunctor}.

  Definition Deriving_FunctorWF_ApplicativeWF : FunctorWF t.
  Proof.
    constructor ; intros ; simpl.
    - rewrite (fapply_respect_fmap id aT) ; simpl.
      rewrite (fapply_unit aT) ; auto.
    - rewrite (fapply_respect_fmap (g '.' f) aT) ; simpl.
      assert (Proper PE_eqv (fmap f aT)).
      { unfold Proper.
        rewrite (fapply_respect_fmap f aT) ; simpl.
        logical_eqv_elim ; auto.
        exact fapply_respect.
        exact funit_respect.
      }
      rewrite (fapply_respect_fmap g (fmap f aT)) ; simpl.
      rewrite (fapply_respect_fmap f aT) ; simpl.
      rewrite (fapply_composition (funit f) (funit g) aT).
      logical_eqv_elim ; auto.
      exact fapply_respect.
      transitivity (fapply (funit (compose g)) (funit f)).
      rewrite (fapply_homomorphism (compose g) f).
      logical_eqv_elim ; auto.
      exact funit_respect.
      exact compose_respect.
      logical_eqv_elim ; auto.
      exact fapply_respect.
      symmetry.
      apply fapply_homomorphism ; auto.
      exact compose_respect.
      exact funit_respect.
    - unfold Proper.
      logical_eqv_intro.
      assert (Proper PE_eqv x). { apply (morph_proper_left H). }
      assert (Proper PE_eqv x0). { apply (morph_proper_left H0). }
      assert (Proper PE_eqv y). { apply (morph_proper_right H). }
      assert (Proper PE_eqv y0). { apply (morph_proper_right H0). }
      rewrite (fapply_respect_fmap x x0) ; simpl.
      rewrite (fapply_respect_fmap y y0) ; simpl.
      logical_eqv_elim ; auto.
      exact fapply_respect.
      exact funit_respect.
  Qed.
End Deriving_FunctorWF_ApplicativeWF.
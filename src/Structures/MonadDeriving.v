Require Import FP.Structures.FUnit.
Require Import FP.Data.Function.
Require Import FP.Data.FunctionStructures.
Require Import FP.Structures.Category.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Applicative.
Require Import FP.Structures.Related.
Require Import FP.Structures.Functor.
Require Import FP.Structures.EqvRel.
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

Section Deriving_ApplicativeWF_MonadWF.
  Variable (m:Type -> Type).
  Context {FUnit_:FUnit m} {MBind_:MBind m}.
  Context {EqvEnv_:EqvEnv}.
  Context {mPER:forall {A} {aPER:PE_R A}, PE_R (m A)}.

  Context {FMap_:FMap m}.

  Class MonadRespFunctor :=
    { bind_resp_fmap :
        forall
          {A} {aER:EqvRel A}
          {B} {bER:EqvRel B}
          (f:A -> B) (f':A -> B) {fP:(env_R ==> env_R) f f'}
          (aM:m A) (aM':m A) {aMP:env_R aM aM'},
            env_R
            (fmap f aM)
            (bind_fmap f' aM')
    }.

  Context {FUnitWF_:FUnitWF m EqvEnv_}.
  Context {MonadWF_:MonadWF m EqvEnv_}.
  Context {MonadRespFunctor_:MonadRespFunctor}.

  Definition Deriving_FunctorWF_MonadWF : FunctorWF m EqvEnv_.
  Proof.
    constructor ; intros.
    - erewrite (bind_resp_fmap id id aT aT').
      simpl.
      promote_fun.
      rewrite category_right_unit_eq.
      apply bind_right_unit.
      reflexivity.
    - simpl.
      erewrite (bind_resp_fmap (g '.' f) (g '.' f) aT aT).
      erewrite (bind_resp_fmap g' g' (fmap f' aT') (fmap f' aT')).
      transitivity (bind_fmap g' (bind_fmap f' aT')).
      + simpl.
        erewrite (bind_associativity
                    (funit '.' f') (funit '.' f')
                    (funit '.' g') (funit '.' g')
                    aT' aT') ; simpl.
        eapply bind_respect ; auto.
        unfold "==>" ; intros ; simpl.
        erewrite (bind_left_unit
                    (funit '.' g') (funit '.' g')
                    (f' y) (f' x)) ; simpl.
        eapply funit_respect.
        eapply gP.
        eapply fP.
        reflexivity.
      + simpl.
        eapply bind_respect.
        * erewrite (bind_resp_fmap f' f' aT' aT') ; simpl.
          reflexivity.
        * unfold "==>" ; intros ; simpl.
          eapply funit_respect.
          eapply (morph_proper_right gP).
          auto.
    - unfold Proper ; intros ; unfold "==>" at 1 ; intros ; unfold "==>" at 1 ; intros.
      erewrite (bind_resp_fmap y y y0 y0).
      eapply bind_resp_fmap ; [|auto].
      exact H.
  Grab Existential Variables.
    reflexivity.
    apply (morph_proper_right H).
    reflexivity.
    apply (morph_proper_right fP).
    apply (morph_proper_right fP) ; symmetry ; exact H.
    unfold "==>" ; intros ; simpl ;
      eapply funit_respect ; eapply (morph_proper_right gP) ; auto.
    reflexivity.
    unfold "==>" ; intros ; simpl ;
      eapply funit_respect ; eapply (morph_proper_right gP) ; auto.
    unfold "==>" ; intros ; simpl ;
      eapply funit_respect ; eapply (morph_proper_right fP) ; auto.
    erewrite (bind_resp_fmap f' f' aT' aT') at 2 ;
      eapply bind_resp_fmap ; [|reflexivity] ; apply (morph_proper_right fP).
    apply (morph_proper_right gP).
    reflexivity.
    unfold "==>" ; intros ; simpl ;
      eapply (morph_proper_left gP) ; eapply (morph_proper_left fP) ; auto.
    auto.
    apply id_respect.
  Grab Existential Variables.
    reflexivity.
    apply (morph_proper_right fP).
  Qed.
End Deriving_FunctorWF_MonadWF.

Section Deriving_FApply_Monad.
  Context {m:Type -> Type} {FUnit_:FUnit m} {MBind_:MBind m}.
  Definition deriving_FApply_Monad {A} {B} : m (A -> B) -> m A -> m B := bind_fapply.
  Definition Deriving_FApply_Monad : FApply m :=
    {| fapply := @deriving_FApply_Monad |}.
End Deriving_FApply_Monad.

Section Deriving_ApplicativeWF_MonadWF.
  Context {m} {FUnit_:FUnit m} {MBind_:MBind m}.
  Variable (EqvEnv_:EqvEnv).
  Context {RPromote:forall {A} {aER:EqvRel A}, EqvRel (m A)}.
  Context {RPromote2:forall {A} {aER:EqvRel A} {B} {bER:EqvRel B}, EqvRel (A -> B)}.
  Context {FUnitWF_:FUnitWF m EqvEnv_}.
  Context {MonadWF_:MonadWF m EqvEnv_}.

  Context {FApply_:FApply m}.
  Class MonadRespApplicative :=
    { bind_resp_fapply :
        forall
          {A} {aER:EqvRel A}
          {B} {bER:EqvRel B}
          (fM:m (A -> B)) (fM':m (A -> B)) {fP:env_R fM fM'}
          (aM:m A) (aM':m A) {aMP:env_R aM aM'},
            env_R
            (fapply fM aM)
            (bind_fapply fM' aM')
    }.
  Context {MonadRespApplicative_:MonadRespApplicative}.

  Definition Deriving_ApplicativeWF_MonadWF : ApplicativeWF m EqvEnv_.
  Proof.
    constructor ; intros.
    - erewrite (bind_resp_fmap id id aT aT').
      simpl.
      promote_fun.
      rewrite category_right_unit_eq.
      apply bind_right_unit.
      reflexivity.
    - simpl.
      erewrite (bind_resp_fmap (g '.' f) (g '.' f) aT aT).
      erewrite (bind_resp_fmap g' g' (fmap f' aT') (fmap f' aT')).
      transitivity (bind_fmap g' (bind_fmap f' aT')).
      + simpl.
        erewrite (bind_associativity
                    (funit '.' f') (funit '.' f')
                    (funit '.' g') (funit '.' g')
                    aT' aT') ; simpl.
        eapply bind_respect ; auto.
        unfold "==>" ; intros ; simpl.
        erewrite (bind_left_unit
                    (funit '.' g') (funit '.' g')
                    (f' y) (f' x)) ; simpl.
        eapply funit_respect.
        eapply gP.
        eapply fP.
        reflexivity.
      + simpl.
        eapply bind_respect.
        * erewrite (bind_resp_fmap f' f' aT' aT') ; simpl.
          reflexivity.
        * unfold "==>" ; intros ; simpl.
          eapply funit_respect.
          eapply (morph_proper_right gP).
          auto.
    - unfold Proper ; intros ; unfold "==>" at 1 ; intros ; unfold "==>" at 1 ; intros.
      erewrite (bind_resp_fmap y y y0 y0).
      eapply bind_resp_fmap ; [|auto].
      exact H.
  Grab Existential Variables.
    reflexivity.
    apply (morph_proper_right H).
    reflexivity.
    apply (morph_proper_right fP).
    apply (morph_proper_right fP) ; symmetry ; exact H.
    unfold "==>" ; intros ; simpl ;
      eapply funit_respect ; eapply (morph_proper_right gP) ; auto.
    reflexivity.
    unfold "==>" ; intros ; simpl ;
      eapply funit_respect ; eapply (morph_proper_right gP) ; auto.
    unfold "==>" ; intros ; simpl ;
      eapply funit_respect ; eapply (morph_proper_right fP) ; auto.
    erewrite (bind_resp_fmap f' f' aT' aT') at 2 ;
      eapply bind_resp_fmap ; [|reflexivity] ; apply (morph_proper_right fP).
    apply (morph_proper_right gP).
    reflexivity.
    unfold "==>" ; intros ; simpl ;
      eapply (morph_proper_left gP) ; eapply (morph_proper_left fP) ; auto.
    auto.
    apply id_respect.
  Grab Existential Variables.
    reflexivity.
    apply (morph_proper_right fP).
  Qed.
End Deriving_FunctorWF_MonadWF.
End Deriving_ApplicativeWF_MonadWF.


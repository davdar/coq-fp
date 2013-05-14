Require Import FP.CoreClasses.
Require Import FP.Categories.
Require Import FP.CoreData.

Import CoreDataNotation.
Import CategoriesNotation.
Import CoreClassesNotation.

Section Deriving_Pointed_Bijection.
  Context {T U:Type -> Type} (from:forall {A}, U A -> T A)
    `{! F_Eqv T ,! F_PER_WF T
     ,! F_Eqv U ,! F_PER_WF U ,! FUnit U ,! PointedWF U
     ,! forall {A} `{! Eqv A ,! PER_WF A }, InjectionRespect (U A) (T A) from eqv eqv
     }.
  Arguments from {A} _.

  Definition deriving_funit_bijection {A} : A -> T A := from '.' funit.
  Arguments deriving_funit_bijection {A} _ /.
  Local Instance Deriving_FUnit_Bijection : FUnit T := { funit := @deriving_funit_bijection }.
  Local Instance Deriving_PointedWF_Bijection : PointedWF T.
  Proof.
    constructor ; intros.
    unfold Proper ; logical_eqv_intro.
    unfold funit ; simpl.
    apply InjectionRespect_eta.
    logical_eqv.
  Qed.
End Deriving_Pointed_Bijection.
Arguments deriving_funit_bijection {T U} from {FUnit0 A} _ /.

Section Deriving_Monad_Bijection.
  Context {T U} (to:forall {A}, T A -> U A) (from:forall {A}, U A -> T A)
    `{! F_Eqv T ,! F_PER_WF T ,! FUnit T ,! PointedWF T
     ,! F_Eqv U ,! F_PER_WF U ,! FUnit U ,! MBind U ,! PointedWF U ,! MonadWF U
     ,! forall {A} `{! Eqv A ,! PER_WF A }, Proper eqv from
     ,! forall {A} `{! Eqv A ,! PER_WF A }, Proper eqv to
     ,! forall {A} `{! Eqv A ,! PER_WF A }, InjectionInverse (U A) (T A) from to eqv
     ,! forall {A} `{! Eqv A ,! PER_WF A }, InjectionInverse (T A) (U A) to from eqv
     }
    ( funit_eqv :
        forall {A} `{! Eqv A ,! PER_WF A } (a:A) `{! Proper eqv a }, funit a ~= to (funit a)
    ).
  Arguments to {A} _.
  Arguments from {A} _.
  Arguments funit_eqv {A _ _} _ {_}.

  Definition deriving_bind_bijection {A B} (aM:T A) (k:A -> T B) : T B :=
    from $ to aM >>= to '.' k.
  Arguments deriving_bind_bijection {A B} _ _ /.
  Local Instance Deriving_MBind_Bijection : MBind T := { bind := @deriving_bind_bijection }.
  Local Instance Deriving_MonadWF_Bijection : MonadWF T.
  Proof.
    constructor ; intros.
    - unfold bind ; simpl.
      rewrite <- funit_eqv ; logical_eqv.
      rewrite bind_left_unit ; logical_eqv ; simpl.
      apply InjectionInverse_inv ; logical_eqv.
    - unfold bind ; simpl.
      unfold compose.
      assert ((fun a => to (ret a)) ~= ret).
      { logical_eqv.
        rewrite <- funit_eqv ; simpl ; logical_eqv.
      }
      rewrite H3.
      rewrite bind_right_unit ; logical_eqv.
      apply InjectionInverse_inv ; logical_eqv.
    - unfold bind ; simpl.
      rewrite InjectionInverse_inv ; logical_eqv.
      rewrite bind_associativity ; logical_eqv ; simpl.
      rewrite H3.
      rewrite InjectionInverse_inv ; logical_eqv.
    - unfold Proper,bind ; logical_eqv_intro ; simpl.
      logical_eqv.
  Qed.
End Deriving_Monad_Bijection.
Arguments deriving_bind_bijection {T U} to from {MBind0 A B} _ _ /.

Section Deriving_MonadCatch_Bijection.
  Context {T U E} (to:forall {A}, T A -> U A) (from:forall {A}, U A -> T A)
    `{! Eqv E ,! PER_WF E
     ,! F_Eqv T ,! F_PER_WF T ,! FUnit T ,! PointedWF T ,! MBind T ,! MonadWF T
     ,! F_Eqv U ,! F_PER_WF U ,! FUnit U ,! MBind U ,! PointedWF U ,! MonadWF U
     ,! MCatch E U ,! MonadCatchWF E U
     ,! forall {A} `{! Eqv A ,! PER_WF A }, Proper eqv from
     ,! forall {A} `{! Eqv A ,! PER_WF A }, Proper eqv to
     ,! forall {A} `{! Eqv A ,! PER_WF A }, InjectionInverse (U A) (T A) from to eqv
     ,! forall {A} `{! Eqv A ,! PER_WF A }, InjectionInverse (T A) (U A) to from eqv
     }
    ( fbind_eqv :
        forall
          {A B} `{! Eqv A ,! PER_WF A ,! Eqv B ,! PER_WF B }
          (aM:T A) `{! Proper eqv aM }
          (k:A -> T B) `{! Proper eqv k},
        aM >>= k ~= from (to aM >>= to '.' k)
    ).
  Arguments to {A} _.
  Arguments from {A} _.

  Definition deriving_throw_bijection {A} : E -> T A :=
    from '.' mthrow.
  Arguments deriving_throw_bijection {A} _ /.
  Definition deriving_catch_bijection {A} (aM:T A) (k:E -> T A) : T A :=
    from $ mcatch (to aM) (to '.' k).
  Arguments deriving_catch_bijection {A} _ _ /.
  Local Instance deriving_MCatch_Bijection : MCatch E T :=
    { mthrow := @deriving_throw_bijection
    ; mcatch := @deriving_catch_bijection
    }.
  Local Instance deriving_MonadCatchWF_Bijection : MonadCatchWF E T.
  Proof.
    constructor ; intros ; unfold mcatch,mthrow ; simpl.
    - rewrite InjectionInverse_inv ; logical_eqv.
      rewrite mcatch_throw_zero ; logical_eqv ; simpl.
      rewrite InjectionInverse_inv ; logical_eqv.
    - rewrite fbind_eqv ; logical_eqv.
      rewrite InjectionInverse_inv ; logical_eqv.
      rewrite mcatch_bind_zero ; logical_eqv.
    - unfold Proper,deriving_throw_bijection ; logical_eqv.
    - unfold Proper,deriving_catch_bijection ; logical_eqv.
  Qed.
End Deriving_MonadCatch_Bijection.

Section Deriving_FApply_MBind.
  Context {m} `{! FUnit m ,! MBind m }.
  Definition deriving_FApply_MBind {A} {B} : m (A -> B) -> m A -> m B := bind_fapply.
  Definition Deriving_FApply_MBind : FApply m := {| fapply := @deriving_FApply_MBind |}.
End Deriving_FApply_MBind.

Section Deriving_ApplicativeWF_MonadWF.
  Context {m}
    `{! FUnit m ,! FApply m ,! MBind m
     ,! F_Eqv m ,! F_PER_WF m
     ,! PointedWF m ,! MonadWF m
     }
    ( bind_respect_fapply :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (fM:m (A -> B)) `{! Proper eqv fM }
          (aM:m A) `{! Proper eqv aM },
        fapply fM aM ~= bind_fapply fM aM
    ).

  Global Instance bind_fapply_respect
      {A} `{! Eqv A ,! PER_WF A }
      {B} `{! Eqv B ,! PER_WF B } :
    Proper eqv (bind_fapply (A:=A) (B:=B)).
  Proof.
    unfold bind_fapply ; logical_eqv.
  Qed.

  Local Instance fapply_respect'
      {A} `{! Eqv A ,! PER_WF A }
      {B} `{! Eqv B ,! PER_WF B } :
    Proper eqv (fapply (A:=A) (B:=B)).
  Proof.
    unfold Proper ; logical_eqv_intro.
    repeat rewrite bind_respect_fapply ; logical_eqv.
  Qed.
  Local Hint Extern 9 (Proper eqv fapply) => apply fapply_respect' : typeclass_instances.

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

Section Deriving_FMap_FApply.
  Context {t} `{! FUnit t ,! FApply t}.
  Definition deriving_FMap_FApply {A} {B} : (A -> B) -> t A -> t B := fapply_fmap.
  Definition Deriving_FMap_FApply : FMap t :=
    {| fmap := @deriving_FMap_FApply |}.
End Deriving_FMap_FApply.

Section Deriving_FunctorWF_ApplicativeWF.
  Context {t}
    `{! FUnit t ,! FMap t ,! FApply t
     ,! F_Eqv t ,! F_PER_WF t
     ,! PointedWF t ,! ApplicativeWF t
     }
    ( fapply_respect_fmap :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (f:A -> B) `{! Proper eqv f }
          (aT:t A) `{! Proper eqv aT },
        fmap f aT ~= fapply_fmap f aT
    ).

  Global Instance fapply_fmap_respect
      {A} `{! Eqv A ,! PER_WF A }
      {B} `{! Eqv B ,! PER_WF B } :
    Proper eqv (fapply_fmap (A:=A) (B:=B)).
  Proof.
    unfold fapply_fmap ; logical_eqv.
  Qed.

  Local Instance fmap_respect'
      {A} `{! Eqv A ,! PER_WF A }
      {B} `{! Eqv B ,! PER_WF B } :
    Proper eqv (fmap (A:=A) (B:=B)).
  Proof.
    unfold Proper ; logical_eqv_intro.
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

Require Import FP.CoreClasses.
Require Import FP.CoreData.
Require Import FP.Classes.

Import CoreDataNotation.
Import ClassesNotation.
Import CoreClassesNotation.

Section Deriving_Monad_Bijection.
  Context {T U} (to:forall {A}, T A -> U A) (from:forall {A}, U A -> T A)
    `{! F_Eqv T ,! F_PER_WF T
     ,! F_Eqv U ,! F_PER_WF U ,! Monad U ,! MonadWF U
     ,! forall {A} `{! Eqv A ,! PER_WF A }, Proper eqv from
     ,! forall {A} `{! Eqv A ,! PER_WF A }, Proper eqv to
     ,! forall {A} `{! Eqv A ,! PER_WF A }, InjectionInverse (U A) (T A) from to eqv
     ,! forall {A} `{! Eqv A ,! PER_WF A }, InjectionInverse (T A) (U A) to from eqv
     }.
  Arguments to {A} _.
  Arguments from {A} _.

  Definition deriving_mret_bijection {A} (a:A) : T A := from (mret a).
  Arguments deriving_mret_bijection {A} _ /.
  Definition deriving_mbind_bijection {A B} (aM:T A) (k:A -> T B) : T B :=
    from $ to aM >>= to '.' k.
  Arguments deriving_mbind_bijection {A B} _ _ /.
  Local Instance Deriving_Monad_Bijection : Monad T :=
    { mret := @deriving_mret_bijection
    ; mbind := @deriving_mbind_bijection
    }.
  Local Instance Deriving_MonadWF_Bijection : MonadWF T.
  Proof.
    constructor ; intros ; unfold mret,mbind ; simpl.
    - rewrite InjectionInverse_inv ; logical_eqv.
      rewrite Monad_left_unit ; logical_eqv ; simpl.
      apply InjectionInverse_inv ; logical_eqv.
    - unfold compose ; simpl.
      transitivity (from (to aM >>= (fun a => mret a))) ; logical_eqv.
      { rewrite InjectionInverse_inv ; logical_eqv. }
      rewrite Monad_right_unit ; logical_eqv.
      rewrite InjectionInverse_inv ; logical_eqv.
    - rewrite InjectionInverse_inv ; logical_eqv.
      rewrite Monad_associativity ; logical_eqv ; simpl.
      rewrite InjectionInverse_inv ; logical_eqv.
    - unfold Proper ; logical_eqv_intro ; simpl ; logical_eqv.
    - unfold Proper ; logical_eqv_intro ; simpl ; logical_eqv.
  Qed.
End Deriving_Monad_Bijection.
Arguments deriving_mret_bijection {T U} from {Monad0 A} a /.
Arguments deriving_mbind_bijection {T U} to from {Monad0 A B} _ _ /.

Section Deriving_MonadCatch_Bijection.
  Context {T U E} (to:forall {A}, T A -> U A) (from:forall {A}, U A -> T A)
    `{! Eqv E ,! PER_WF E
     ,! F_Eqv T ,! F_PER_WF T ,! Monad T ,! MonadWF T
     ,! F_Eqv U ,! F_PER_WF U ,! Monad U ,! MonadWF U ,! MonadCatch E U ,! MonadCatchWF E U
     ,! forall {A} `{! Eqv A ,! PER_WF A }, Proper eqv from
     ,! forall {A} `{! Eqv A ,! PER_WF A }, Proper eqv to
     ,! forall {A} `{! Eqv A ,! PER_WF A }, InjectionInverse (U A) (T A) from to eqv
     ,! forall {A} `{! Eqv A ,! PER_WF A }, InjectionInverse (T A) (U A) to from eqv
     }
    ( mret_eqv :
        forall {A} `{! Eqv A ,! PER_WF A } (a:A) `{! Proper eqv a }, mret a ~= from (mret a)
    )
    ( mbind_eqv :
        forall
          {A B} `{! Eqv A ,! PER_WF A ,! Eqv B ,! PER_WF B }
          (aM:T A) `{! Proper eqv aM }
          (k:A -> T B) `{! Proper eqv k},
        aM >>= k ~= from (to aM >>= to '.' k)
    ).
  Arguments to {A} _.
  Arguments from {A} _.

  Definition deriving_mthrow_bijection {A} : E -> T A :=
    from '.' mthrow.
  Arguments deriving_mthrow_bijection {A} _ /.
  Definition deriving_mcatch_bijection {A} (aM:T A) (k:E -> T A) : T A :=
    from $ mcatch (to aM) (to '.' k).
  Arguments deriving_mcatch_bijection {A} _ _ /.
  Local Instance deriving_MonadCatch_Bijection : MonadCatch E T :=
    { mthrow := @deriving_mthrow_bijection
    ; mcatch := @deriving_mcatch_bijection
    }.
  Local Instance deriving_MonadCatchWF_Bijection : MonadCatchWF E T.
  Proof.
    constructor ; intros ; unfold mcatch,mthrow ; simpl.
    - rewrite mret_eqv ; logical_eqv.
      rewrite InjectionInverse_inv ; logical_eqv.
      rewrite MonadCatch_mcatch_mret ; logical_eqv.
    - rewrite InjectionInverse_inv ; logical_eqv.
      rewrite MonadCatch_mcatch_mthrow ; logical_eqv ; simpl.
      rewrite InjectionInverse_inv ; logical_eqv.
    - rewrite mbind_eqv ; logical_eqv.
      rewrite InjectionInverse_inv ; logical_eqv.
      rewrite MonadCatch_mbind_mthrow ; logical_eqv.
    - unfold Proper ; logical_eqv_intro ; simpl ; logical_eqv.
    - unfold Proper ; logical_eqv_intro ; simpl ; logical_eqv.
  Qed.
End Deriving_MonadCatch_Bijection.

Section Deriving_Applicative_Monad.
  Context {m} `{! Monad m }.
  Local Instance Deriving_Applicative_Monad : Applicative m :=
    { fret := @mret _ _
    ; fapply := @mbind_fapply _ _
    }.
End Deriving_Applicative_Monad.

Section Deriving_ApplicativeWF_MonadWF.
  Context {m}
    `{! F_Eqv m ,! F_PER_WF m ,! Applicative m ,! Monad m ,! MonadWF m
     }
    ( fret_eqv :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          (a:A) `{! Proper eqv a },
        fret a ~= mret a
    )
    ( fapply_eqv :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          {B} `{! Eqv B ,! PER_WF B }
          (fM:m (A -> B)) `{! Proper eqv fM }
          (aM:m A) `{! Proper eqv aM },
        fapply fM aM ~= mbind_fapply fM aM
    ).

  Global Instance mbind_fapply_Proper
      {A} `{! Eqv A ,! PER_WF A }
      {B} `{! Eqv B ,! PER_WF B } :
    Proper eqv (mbind_fapply (A:=A) (B:=B)).
  Proof.
    unfold mbind_fapply ; logical_eqv.
  Qed.

  Local Instance fret_Proper'
      {A} `{! Eqv A ,! PER_WF A } :
    Proper eqv (fret (A:=A)).
  Proof.
    unfold Proper ; logical_eqv_intro.
    repeat rewrite fret_eqv ; logical_eqv.
  Qed.

  Local Instance fapply_Proper'
      {A} `{! Eqv A ,! PER_WF A }
      {B} `{! Eqv B ,! PER_WF B } :
    Proper eqv (fapply (A:=A) (B:=B)).
  Proof.
    unfold Proper ; logical_eqv_intro.
    repeat rewrite fapply_eqv ; logical_eqv.
  Qed.
  Local Hint Extern 9 (Proper eqv fapply) => apply fapply_Proper' : typeclass_instances.

  Definition Deriving_ApplicativeWF_MonadWF : ApplicativeWF m.
  Proof.
    constructor ; intros ; eauto with typeclass_instances
    ; repeat (rewrite fret_eqv ; logical_eqv) ; simpl
    ; repeat (rewrite fapply_eqv ; logical_eqv) ; simpl.
    - rewrite Monad_left_unit ; logical_eqv ; simpl.
      rewrite Monad_right_unit ; auto.
    - repeat (rewrite Monad_associativity ; logical_eqv) ; simpl.
      repeat (rewrite Monad_left_unit ; logical_eqv) ; simpl.
      repeat (rewrite Monad_associativity ; logical_eqv).
      repeat (rewrite Monad_left_unit ; logical_eqv) ; simpl.
      repeat (rewrite Monad_associativity ; logical_eqv).
      repeat (rewrite Monad_left_unit ; logical_eqv) ; simpl.
      logical_eqv.
    - repeat (rewrite Monad_left_unit ; logical_eqv) ; simpl.
    - repeat (rewrite Monad_left_unit ; logical_eqv) ; simpl.
      logical_eqv.
  Qed.
End Deriving_ApplicativeWF_MonadWF.

Section Deriving_Functor_Applicative.
  Context {t} `{! Applicative t }.
  Local Instance Deriving_Functor_Applicative : Functor t := { fmap := @fapply_fmap _ _ }.
End Deriving_Functor_Applicative.

Section Deriving_FunctorWF_ApplicativeWF.
  Context {t}
    `{! F_Eqv t ,! F_PER_WF t ,! Functor t ,! Applicative t ,! ApplicativeWF t }
    ( fmap_eqv :
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
    repeat rewrite fmap_eqv ; logical_eqv.
  Qed.

  Definition Deriving_FunctorWF_ApplicativeWF : FunctorWF t.
  Proof.
    constructor ; intros ; simpl ; eauto with typeclass_instances
    ; repeat (rewrite fmap_eqv ; logical_eqv) ; simpl.
    - rewrite Applicative_unit ; logical_eqv.
    - rewrite Applicative_composition ; logical_eqv ; simpl.
      repeat (rewrite Applicative_homomorphism ; logical_eqv) ; simpl.
  Qed.
End Deriving_FunctorWF_ApplicativeWF.

Section Deriving_Pointed_Applicative.
  Context {t} `{! Applicative t }.
  Local Instance Deriving_Pointed_Applicative : Pointed t := { point := @fret _ _ }.
End Deriving_Pointed_Applicative.
  
Section Deriving_PointedWF_ApplicativeWF.
  Context {t}
    `{! F_Eqv t ,! F_PER_WF t ,! Pointed t ,! Applicative t ,! ApplicativeWF t }
    ( point_eqv :
        forall
          {A} `{! Eqv A ,! PER_WF A }
          (a:A) `{! Proper eqv a },
        point a ~= fret a
    ).

  Local Instance Deriving_PointedWF_ApplicativeWF : PointedWF t.
  Proof.
    constructor ; intros ; unfold Proper ; logical_eqv_intro.
    repeat rewrite point_eqv ; logical_eqv.
  Qed.
End Deriving_PointedWF_ApplicativeWF.

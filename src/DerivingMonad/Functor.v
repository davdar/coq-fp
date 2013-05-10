Require Import FP.Categories.
Require Import FP.CoreClasses.
Require Import FP.DerivingMonad.Core.

Class DM_FunctorI (T:Type -> Type) (U:Type -> Type) :=
  { DM_F_T_F_Eqv :> F_Eqv T
  ; DM_F_T_F_PER_WF :> F_PER_WF T
  ; DM_F_U_F_Eqv :> F_Eqv U
  ; DM_F_U_F_PER_WF :> F_PER_WF U
  ; DM_F_U_FUnit :> FUnit U
  ; DM_F_U_PointedWF :> PointedWF U
  ; DM_F_U_MBind :> MBind U
  ; DM_F_U_MonadWF :> MonadWF U
  }.

Module Type DM_Functor_Arg.
  Parameter T : Type -> Type.
  Parameter U : Type -> Type.
  Parameter to : forall {A}, T A -> U A.
  Parameter from : forall {A}, U A -> T A.
  Parameter _DM_FunctorI : DM_FunctorI T U.
  Parameter IR_from_eqv :
    forall {A} `{! Eqv A ,! PER_WF A },
    InjectionRespect (U A) (T A) from eqv eqv.
  Parameter II_to_from_eqv :
    forall {A} `{! Eqv A ,! PER_WF A },
    InjectionInverse (T A) (U A) to from eqv.
  Parameter II_from_from_eqv :
    forall {A} `{! Eqv A ,! PER_WF A },
    InjectionInverse (U A) (T A) from to eqv.
  Parameter Proper_to_eqv :
    forall {A} `{! Eqv A ,! PER_WF A },
    Proper eqv (@to A).
  Parameter Proper_from_eqv :
    forall {A} `{! Eqv A ,! PER_WF A },
    Proper eqv (@from A).
End DM_Functor_Arg.

Module DM_Functor (M:DM_Functor_Arg).
  Import M.
  Arguments T / _ .
  Arguments U / _ .
  Arguments to {A} / _ .
  Arguments from {A} / _ .

  Section Pointed.
    Global Instance _FUnit : FUnit T := Deriving_FUnit_Bijection (@from).

    Global Instance _PointedWF : PointedWF T := Deriving_PointedWF_Bijection (@from).
  End Pointed.

  Section Monad.
    Global Instance _MBind : MBind T := Deriving_MBind_Bijection (@to) (@from).

    Global Instance _MonadWF : MonadWF T.
    Proof.
      apply (Deriving_MonadWF_Bijection (@to) (@from)) ; intros.
      unfold funit at 2 ; simpl.
      rewrite InjectionInverse_inv ; logical_eqv.
    Qed.
  End Monad.

  Section Applicative.
    Global Instance _FApply : FApply T := Deriving_FApply_MBind.

    Global Instance _ApplicativeWF : ApplicativeWF T.
    Proof.
      apply Deriving_ApplicativeWF_MonadWF ; intros.
      unfold fapply ; simpl ; logical_eqv.
    Qed.
  End Applicative.

  Section Functor.
    Global Instance _FMap : FMap T := Deriving_FMap_FApply.

    Global Instance _FunctorWF : FunctorWF T.
    Proof.
      apply Deriving_FunctorWF_ApplicativeWF ; intros.
      unfold fmap ; simpl ; logical_eqv.
    Qed.
  End Functor.
End DM_Functor.
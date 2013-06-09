Require Import FP.Classes.
Require Import FP.CoreClasses.
Require Import FP.DerivingMonad.Core.

Class DM_FunctorI (T:Type -> Type) (U:Type -> Type) :=
  { DM_F_T_F_Eqv :> F_Eqv T
  ; DM_F_T_F_PER_WF :> F_PER_WF T
  ; DM_F_U_F_Eqv :> F_Eqv U
  ; DM_F_U_F_PER_WF :> F_PER_WF U
  ; DM_F_U_Monad :> Monad U
  ; DM_F_U_MonadWF :> MonadWF U
  }.

Class DM_FunctorI' T U := { dm_functor_i' : DM_FunctorI T U }.

Module Type DM_Functor_Arg.
  Local Existing Instance dm_functor_i'.

  Parameter T : Type -> Type.
  Parameter U : Type -> Type.
  Parameter to : forall {A}, T A -> U A.
  Parameter from : forall {A}, U A -> T A.
  Parameter _DM_FunctorI : DM_FunctorI' T U.
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
  Local Existing Instance dm_functor_i'.

  Import M.
  Arguments T / _ .
  Arguments U / _ .
  Arguments to {A} / _ .
  Arguments from {A} / _ .
  Local Existing Instance DM_F_T_F_Eqv.
  Local Existing Instance DM_F_T_F_PER_WF.
  Local Existing Instance DM_F_U_F_Eqv.
  Local Existing Instance DM_F_U_F_PER_WF.
  Local Existing Instance DM_F_U_Monad.
  Local Existing Instance DM_F_U_MonadWF.

  Section Monad.
    Global Instance _Monad : Monad T := Deriving_Monad_Bijection (@to) (@from).

    Global Instance _MonadWF : MonadWF T := Deriving_MonadWF_Bijection (@to) (@from).
  End Monad.

  Section Applicative.
    Global Instance _Applicative : Applicative T := Deriving_Applicative_Monad.

    Global Instance _ApplicativeWF : ApplicativeWF T.
    Proof.
      apply Deriving_ApplicativeWF_MonadWF ; intros.
      - unfold fret ; simpl ; logical_eqv.
      - unfold fapply ; simpl ; logical_eqv.
    Qed.
  End Applicative.

  Section Functor.
    Global Instance _Functor : Functor T := Deriving_Functor_Applicative.

    Global Instance _FunctorWF : FunctorWF T.
    Proof.
      apply Deriving_FunctorWF_ApplicativeWF ; intros.
      unfold fmap ; simpl ; logical_eqv.
    Qed.
  End Functor.

  Section Pointed.
    Global Instance _Pointed : Pointed T := Deriving_Pointed_Applicative.

    Global Instance _PointedWF : PointedWF T.
    Proof.
      apply Deriving_PointedWF_ApplicativeWF ; intros.
      unfold point ; simpl ; logical_eqv.
    Qed.
  End Pointed.

End DM_Functor.

Class DMError_FunctorI
    (E:Type) (T:Type -> Type) (U:Type -> Type)
    `{! F_Eqv U ,! F_PER_WF U ,! Monad U } :=
  { DMError_Idx_E_Eqv : Eqv E
  ; DMError_Idx_E_PER_WF : PER_WF E
  ; DMError_Idx_U_MonadCatch : MonadCatch E U
  ; DMError_Idx_U_MonadCatchWF : MonadCatchWF E U
  }.

Module Type DMError_Functor_Arg.
  Local Existing Instance dm_functor_i'.

  Include DM_Functor_Arg.
  Parameter E : Type.
  Parameter _DMError_FunctorI : DMError_FunctorI E T U.
End DMError_Functor_Arg.

Module DMError_Functor (M:DMError_Functor_Arg).
  Local Existing Instance dm_functor_i'.
  Local Existing Instance DMError_Idx_E_Eqv.
  Local Existing Instance DMError_Idx_U_MonadCatch.
  Local Existing Instance DMError_Idx_U_MonadCatchWF.

  Import M.
  Module DM := DM_Functor M.
  Import DM.

  Arguments T / _.
  Arguments U / _.
  Arguments E /.
  Arguments to {A} / _ .
  Arguments from {A} / _ .

  Section MonadError.
    Global Instance _MonadCatch : MonadCatch E T := deriving_MonadCatch_Bijection (@to) (@from).
    Global Instance _MonadCatchWF : MonadCatchWF E T.
    Proof.
      apply (deriving_MonadCatchWF_Bijection (@to) (@from)) ; intros.
      - unfold mret at 1 ; simpl ; logical_eqv.
      - unfold mbind at 1 ; simpl ; logical_eqv.
    Qed.
  End MonadError.
End DMError_Functor.
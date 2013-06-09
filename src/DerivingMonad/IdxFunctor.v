Require Import FP.Classes.
Require Import FP.CoreClasses.
Require Import FP.DerivingMonad.Core.

Class DM_IdxFunctorI (T:Type -> Type -> Type) (U:Type -> Type -> Type) :=
  { DM_Idx_T_F_Eqv :> forall {I} `{! Eqv I }, F_Eqv (T I)
  ; DM_Idx_T_F_PER_WF :> forall {I} `{! Eqv I ,! PER_WF I }, F_PER_WF (T I)
  ; DM_Idx_U_F_Eqv :> forall {I} `{! Eqv I }, F_Eqv (U I)
  ; DM_Idx_U_F_PER_WF :> forall {I} `{! Eqv I ,! PER_WF I }, F_PER_WF (U I)
  ; DM_Idx_U_Monad :> forall {I}, Monad (U I)
  ; DM_Idx_U_MonadWF :> forall {I} `{! Eqv I ,! PER_WF I }, MonadWF (U I)
  }.

Class DM_IdxFunctorI' T U := { dm_idx_functor_i : DM_IdxFunctorI T U }.

Module Type DM_IdxFunctor_Arg.
  Local Existing Instance dm_idx_functor_i.

  Parameter T : Type -> Type -> Type.
  Parameter U : Type -> Type -> Type.
  Parameter to : forall {I A}, T I A -> U I A.
  Parameter from : forall {I A}, U I A -> T I A.
  Parameter _DM_IdxFunctorI : DM_IdxFunctorI' T U.
  Parameter IR_from_eqv :
    forall {I A} `{! Eqv I ,! PER_WF I ,! Eqv A ,! PER_WF A },
    InjectionRespect (U I A) (T I A) from eqv eqv.
  Parameter II_to_from_eqv :
    forall {I A} `{! Eqv I ,! PER_WF I ,! Eqv A ,! PER_WF A },
    InjectionInverse (T I A) (U I A) to from eqv.
  Parameter II_from_from_eqv :
    forall {I A} `{! Eqv I ,! PER_WF I ,! Eqv A ,! PER_WF A },
    InjectionInverse (U I A) (T I A) from to eqv.
  Parameter Proper_to_eqv :
    forall {I A} `{! Eqv I ,! PER_WF I ,! Eqv A ,! PER_WF A },
    Proper eqv (@to I A).
  Parameter Proper_from_eqv :
    forall {I A} `{! Eqv I ,! PER_WF I ,! Eqv A ,! PER_WF A },
    Proper eqv (@from I A).
End DM_IdxFunctor_Arg.

Module DM_IdxFunctor (M:DM_IdxFunctor_Arg).
  Local Existing Instance dm_idx_functor_i.

  Import M.
  Arguments T / _ _ .
  Arguments U / _ _ .
  Arguments to {I A} / _ .
  Arguments from {I A} / _ .

  Section I.
    Context {I:Type}.

    Section Monad.
      Global Instance _Monad : Monad (T I) := Deriving_Monad_Bijection (@to I) (@from I).

      Context `{! Eqv I ,! PER_WF I }.

      Global Instance _MonadWF : MonadWF (T I) := Deriving_MonadWF_Bijection (@to I) (@from I).
    End Monad.

    Section Applicative.
      Global Instance _Applicative : Applicative (T I) := Deriving_Applicative_Monad.

      Context `{! Eqv I ,! PER_WF I }.

      Global Instance _ApplicativeWF : ApplicativeWF (T I).
      Proof.
        apply Deriving_ApplicativeWF_MonadWF ; intros.
        - unfold fret ; simpl ; logical_eqv.
        - unfold fapply ; simpl ; logical_eqv.
      Qed.
    End Applicative.

    Section Functor.
      Global Instance _Functor : Functor (T I) := Deriving_Functor_Applicative.

      Context `{! Eqv I ,! PER_WF I }.

      Global Instance _FunctorWF : FunctorWF (T I).
      Proof.
        apply Deriving_FunctorWF_ApplicativeWF ; intros.
        unfold fmap ; simpl ; logical_eqv.
      Qed.
    End Functor.

    Section Pointed.
      Global Instance _Pointed : Pointed (T I) := Deriving_Pointed_Applicative.

      Context `{! Eqv I ,! PER_WF I }.

      Global Instance _PointedWF : PointedWF (T I).
      Proof.
        apply Deriving_PointedWF_ApplicativeWF ; intros.
        unfold point ; simpl ; logical_eqv.
      Qed.
    End Pointed.

  End I.
End DM_IdxFunctor.

Class DMError_IdxFunctorI
    (T:Type -> Type -> Type) (U:Type -> Type -> Type)
    `{! forall {I} `{! Eqv I }, F_Eqv (U I)
     ,! forall {I} `{! Eqv I ,! PER_WF I }, F_PER_WF (U I)
     ,! forall {I}, Monad (U I)
     } :=
  { DMError_Idx_U_MonadCatch : forall {I}, MonadCatch I (U I)
  ; DMError_Idx_U_MonadCatchWF : forall {I} `{! Eqv I ,! PER_WF I}, MonadCatchWF I (U I)
  }.

Module Type DMError_IdxFunctor_Arg.
  Local Existing Instance dm_idx_functor_i.

  Include DM_IdxFunctor_Arg.
  Parameter _DMError_IdxFunctorI : DMError_IdxFunctorI T U.
End DMError_IdxFunctor_Arg.

Module DMError_IdxFunctor (M:DMError_IdxFunctor_Arg).
  Local Existing Instance dm_idx_functor_i.
  Local Existing Instance DMError_Idx_U_MonadCatch.
  Local Existing Instance DMError_Idx_U_MonadCatchWF.

  Import M.
  Module DM := DM_IdxFunctor M.
  Import DM.

  Arguments T / _ _ .
  Arguments U / _ _ .
  Arguments to {I A} / _ .
  Arguments from {I A} / _ .

  Section MonadError.
    Context {I:Type} `{! Eqv I ,! PER_WF I }.

    Global Instance _MonadCatch : MonadCatch I (T I) := deriving_MonadCatch_Bijection (@to I) (@from I).
    Global Instance _MonadCatchWF : MonadCatchWF I (T I).
    Proof.
      apply (deriving_MonadCatchWF_Bijection (@to I) (@from I)) ; intros.
      - unfold mret at 1 ; simpl ; logical_eqv.
      - unfold mbind at 1 ; simpl ; logical_eqv.
    Qed.
  End MonadError.
End DMError_IdxFunctor.
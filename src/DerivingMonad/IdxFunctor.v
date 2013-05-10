Require Import FP.Categories.
Require Import FP.CoreClasses.
Require Import FP.DerivingMonad.Core.

Class DM_IdxFunctorI (T:Type -> Type -> Type) (U:Type -> Type -> Type) :=
  { DM_Idx_T_F_Eqv :> forall {I} `{! Eqv I }, F_Eqv (T I)
  ; DM_Idx_T_F_PER_WF :> forall {I} `{! Eqv I ,! PER_WF I }, F_PER_WF (T I)
  ; DM_Idx_U_F_Eqv :> forall {I} `{! Eqv I }, F_Eqv (U I)
  ; DM_Idx_U_F_PER_WF :> forall {I} `{! Eqv I ,! PER_WF I }, F_PER_WF (U I)
  ; DM_Idx_U_FUnit :> forall {I}, FUnit (U I)
  ; DM_Idx_U_PointedWF :> forall {I} `{! Eqv I ,! PER_WF I }, PointedWF (U I)
  ; DM_Idx_U_MBind :> forall {I}, MBind (U I)
  ; DM_Idx_U_MonadWF :> forall {I} `{! Eqv I ,! PER_WF I }, MonadWF (U I)
  }.

Module Type DM_IdxFunctor_Arg.
  Parameter T : Type -> Type -> Type.
  Parameter U : Type -> Type -> Type.
  Parameter to : forall {I A}, T I A -> U I A.
  Parameter from : forall {I A}, U I A -> T I A.
  Parameter _DM_IdxFunctorI : DM_IdxFunctorI T U.
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
  Import M.
  Arguments T / _ _ .
  Arguments U / _ _ .
  Arguments to {I A} / _ .
  Arguments from {I A} / _ .

  Section I.
    Context {I:Type}.

    Section Pointed.
      Global Instance _FUnit : FUnit (T I) := Deriving_FUnit_Bijection (@from I).

      Context `{! Eqv I ,! PER_WF I }.

      Global Instance _PointedWF : PointedWF (T I) := Deriving_PointedWF_Bijection (@from I).
    End Pointed.

    Section Monad.
      Global Instance _MBind : MBind (T I) := Deriving_MBind_Bijection (@to I) (@from I).

      Context `{! Eqv I ,! PER_WF I }.

      Global Instance _MonadWF : MonadWF (T I).
      Proof.
        apply (Deriving_MonadWF_Bijection (@to I) (@from I)) ; intros.
        unfold funit at 2 ; simpl.
        rewrite InjectionInverse_inv ; logical_eqv.
      Qed.
    End Monad.

    Section Applicative.
      Global Instance _FApply : FApply (T I) := Deriving_FApply_MBind.

      Context `{! Eqv I ,! PER_WF I }.

      Global Instance _ApplicativeWF : ApplicativeWF (T I).
      Proof.
        apply Deriving_ApplicativeWF_MonadWF ; intros.
        unfold fapply ; simpl ; logical_eqv.
      Qed.
    End Applicative.

    Section Functor.
      Global Instance _FMap : FMap (T I) := Deriving_FMap_FApply.

      Context `{! Eqv I ,! PER_WF I }.

      Global Instance _FunctorWF : FunctorWF (T I).
      Proof.
        apply Deriving_FunctorWF_ApplicativeWF ; intros.
        unfold fmap ; simpl ; logical_eqv.
      Qed.
    End Functor.
  End I.
End DM_IdxFunctor.
Require Import FP.Data.Error.
Require Import FP.Data.ErrorT.
Require Import FP.Data.Identity.
Require Import FP.DerivingMonad.
Require Import FP.CoreData.
Require Import FP.CoreClasses.
Require Import FP.Categories.

Import CoreDataNotation.
Import CoreClassesNotation.

Section error_b_Bijection.
  Context {E A} `{! Eqv E ,! Eqv A }.
  Definition error_to_error_b : error E A -> error_b E A :=
    ErrorT '.' Identity.
  Arguments error_to_error_b / _.
  Definition error_b_to_error : error_b E A -> error E A :=
    un_identity '.' un_error_t.
  Arguments error_b_to_error / _.
  Global Instance error_IR_error_b_to_error
    : InjectionRespect (error_b E A) (error E A) error_b_to_error eqv eqv.
  Proof.
    constructor ; unfold Proper,"==>","<==" ; intros.
    - destruct x as [x],y as [y] ; simpl in *.
      unfold eqv in H ; simpl in H.
      apply InjectionRespect_eta ; auto.
    - destruct x as [x],y as [y] ; simpl in *.
      unfold eqv ; simpl.
      apply InjectionRespect_beta ; auto.
  Qed.
  Global Instance error_to_error_b_Proper : Proper eqv error_to_error_b.
  Proof.
    unfold Proper ; logical_eqv_intro ; simpl ; logical_eqv.
  Qed.
  Global Instance error_b_to_error_Proper : Proper eqv error_b_to_error.
  Proof.
    unfold Proper ; logical_eqv_intro ; simpl ; logical_eqv.
  Qed.
  Context `{! PER_WF E ,! PER_WF A }.
  Global Instance error_II_error_to_error_b
    : InjectionInverse (error E A) (error_b E A) error_to_error_b error_b_to_error eqv.
  Proof.
    constructor ; intros ; simpl ; logical_eqv.
  Qed.
  Global Instance error_II_error_b_to_error
    : InjectionInverse (error_b E A) (error E A) error_b_to_error error_to_error_b eqv.
  Proof.
    constructor ; intros ; simpl.
    destruct x as [x] ; destruct x as [x] ; simpl ; logical_eqv.
  Qed.
End error_b_Bijection.

Module error_DM_Arg <: DM_IdxFunctor_Arg.
  Definition T := error.
  Definition U := error_b.
  Definition to : forall {I A}, T I A -> U I A := @error_to_error_b.
  Definition from : forall {I A}, U I A -> T I A := @error_b_to_error.
  Definition _DM_IdxFunctorI : DM_IdxFunctorI T U.
  Proof. econstructor ; eauto with typeclass_instances. Defined.
  Definition IR_from_eqv :
    forall {I A} `{! Eqv I ,! PER_WF I ,! Eqv A ,! PER_WF A },
    InjectionRespect (U I A) (T I A) from eqv eqv := _.
  Definition II_to_from_eqv :
    forall {I A} `{! Eqv I ,! PER_WF I ,! Eqv A ,! PER_WF A },
    InjectionInverse (T I A) (U I A) to from eqv := _.
  Definition II_from_from_eqv :
    forall {I A} `{! Eqv I ,! PER_WF I ,! Eqv A ,! PER_WF A },
    InjectionInverse (U I A) (T I A) from to eqv := _.
  Definition Proper_to_eqv :
    forall {I A} `{! Eqv I ,! PER_WF I ,! Eqv A ,! PER_WF A },
    Proper eqv (@to I A) := _.
  Definition Proper_from_eqv :
    forall {I A} `{! Eqv I ,! PER_WF I ,! Eqv A ,! PER_WF A },
    Proper eqv (@from I A) := _.
End error_DM_Arg.

Module error_DM := DM_IdxFunctor error_DM_Arg.
Import error_DM.
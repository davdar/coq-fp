Require Import FP.CoreClasses.
Require Import FP.Classes.
Require Import FP.DerivingEverything.
Require Import FP.Data.Type.
Require Import FP.Data.Sum.

Import ClassesNotation.
Import CoreClassesNotation.

Inductive error E A :=
  | Failure : E -> error E A
  | Success : A -> error E A.
Arguments Failure {E A} _.
Arguments Success {E A} _.

Section error_Bijection.
  Context {E A:Type}.

  Definition error_to_sum (aM:error E A) : E + A :=
    match aM with
    | Failure e => inl e
    | Success a => inr a
    end.
  Global Instance IR_error_to_sum_eq
    : InjectionRespect (error E A) (E+A) error_to_sum eq eq.
  Proof.
    constructor ; unfold Proper ; simpl in * ; intros ; try congruence.
    destruct x,y ; simpl in * ; congruence.
  Qed.

  Definition sum_to_error (aM:E+A) : error E A :=
    match aM with
    | inl e => Failure e
    | inr a => Success a
    end.
  Global Instance II_sum_to_error_eq
    : InjectionInverse (E+A) (error E A) sum_to_error error_to_sum eq.
  Proof.
    constructor ; intros.
    destruct x ; simpl in * ; auto.
  Qed.
End error_Bijection.

Module error_DE_Arg <: DE_IdxFunctor_Arg.
  Definition T := error.
  Definition U := sum.
  Definition to : forall {E A}, T E A -> U E A := @error_to_sum.
  Definition from : forall {E A}, U E A -> T E A := @sum_to_error.
  Definition IR_to {E A} : InjectionRespect (T E A) (U E A) to eq eq := _.
  Definition II_from {E A} : InjectionInverse (U E A) (T E A) from to eq := _.
  Definition _DE_IdxFunctorI : DE_IdxFunctorI' U.
  Proof. econstructor ; econstructor ; eauto with typeclass_instances. Defined.
End error_DE_Arg.
Module error_DE := DE_IdxFunctor error_DE_Arg.
Import error_DE.

Section IR.
  Context {E A C} `{! Eqv E ,! PER_WF E ,! Eqv A ,! PER_WF A ,! Eqv C ,! PER_WF C }.

  Global Instance IR_Failure_eqv : InjectionRespect E (error E A) Failure eqv eqv.
  Proof.
    constructor ; unfold Proper,"==>","<==" ; intros ; simpl.
    - apply InjectionRespect_beta ; simpl.
      apply InjectionRespect_eta ; auto.
    - apply InjectionRespect_eta in H ; simpl in H.
      apply InjectionRespect_beta in H ; auto.
  Qed.

  Global Instance Failure_Proper : Proper eqv (@Failure E A) := Proper_inj.

  Global Instance IR_Success_eqv : InjectionRespect A (error E A) Success eqv eqv.
    constructor ; unfold Proper,"==>","<==" ; intros ; simpl.
    - apply InjectionRespect_beta ; simpl.
      apply InjectionRespect_eta ; auto.
    - apply InjectionRespect_eta in H ; simpl in H.
      apply InjectionRespect_beta in H ; auto.
  Qed.

  Global Instance Success_Proper : Proper eqv (@Success E A) := Proper_inj.
End IR.

Definition error_elim {E A C} (aM:error E A) (ef:E -> C) (af:A -> C) : C :=
  match aM with
  | Failure e => ef e
  | Success a => af a
  end.
Section error_elim_Proper.
  Context {E A C} `{! Eqv E ,! PER_WF E ,! Eqv A ,! PER_WF A ,! Eqv C ,! PER_WF C }.
  Global Instance error_elim_Proper : Proper eqv (@error_elim E A C).
  Proof.
    unfold Proper ; logical_eqv_intro.
    destruct x,y ; simpl ; logical_eqv.
    - apply InjectionRespect_beta in H ; auto.
    - inversion H.
    - inversion H.
    - apply InjectionRespect_beta in H ; auto.
  Qed.
End error_elim_Proper.
Definition from_elim {E A} (ef:E -> A) (aM:error E A) : A := error_elim aM ef id.

Ltac fold_error :=
  match goal with
  | [ |- context
         [ match ?aM with
           | Failure e => (@?ef e)
           | Success a => (@?af a)
           end
         ]
    ] => fold (error_elim aM ef af)
  end.
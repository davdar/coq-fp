Require Import FP.CoreClasses.
Require Import FP.Categories.
Require Import FP.Deriving.
Require Import FP.Data.Type.
Require Import FP.Data.Sum.

Import CategoriesNotation.

Inductive Error E A :=
  | Failure : E -> Error E A
  | Success : A -> Error E A.
Arguments Failure {E A} _.
Arguments Success {E A} _.

Section error_Bijection.
  Context {E A:Type}.

  Definition error_to_sum (aM:Error E A) : E + A :=
    match aM with
    | Failure e => inl e
    | Success a => inr a
    end.
  Global Instance IR_error_to_sum_eq
    : InjectionRespect (Error E A) (E+A) error_to_sum eq eq.
  Proof.
    constructor ; unfold Proper ; simpl in * ; intros ; try congruence.
    destruct x,y ; simpl in * ; congruence.
  Qed.

  Definition sum_to_error (aM:E+A) : Error E A :=
    match aM with
    | inl e => Failure e
    | inr a => Success a
    end.
  Global Instance II_sum_to_error_eq
    : InjectionInverse (E+A) (Error E A) sum_to_error error_to_sum eq.
  Proof.
    constructor ; intros.
    destruct x ; simpl in * ; auto.
  Qed.
End error_Bijection.

Module error_DerivingEverything_Bifunctor_Arg <: DerivingEverything_Bifunctor_Arg.
  Definition T E A := Error E A.
  Definition U E A := E+A.
  Definition to {E A} (x:T E A) := error_to_sum x.
  Definition from {E A} (x:U E A) := sum_to_error x.
  Definition InjResp {E A} : InjectionRespect (T E A) (U E A) to eq eq := _.
  Definition InjInv {E A} : InjectionInverse (U E A) (T E A) from to eq := _.
  Definition _DerivingEverything_BifunctorI : DerivingEverything_BifunctorI U.
  Proof. econstructor ; eauto with typeclass_instances. Defined.
End error_DerivingEverything_Bifunctor_Arg.

Module error_DerivingEverything_Bifunctor :=
  DerivingEverything_Bifunctor error_DerivingEverything_Bifunctor_Arg.
Import error_DerivingEverything_Bifunctor.
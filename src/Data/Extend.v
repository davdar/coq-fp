Require Import FP.Data.Type.
Require Import FP.Classes.
Require Import FP.CoreData.
Require Import FP.CoreClasses.
Require Import FP.DerivingEverything.
Require Import FP.Data.Sum.
Require Import FP.Data.Unit.

Import ClassesNotation.
Import CoreDataNotation.
Import CoreClassesNotation.

Inductive extend A :=
  | ExtendBot : extend A
  | Extend : A -> extend A
  | ExtendTop : extend A.
Arguments ExtendBot {A}.
Arguments Extend {A} _.
Arguments ExtendTop {A}.

Section extend_Bijection.
  Definition extend_to_sum {A} (e:extend A) : unit + A + unit :=
    match e with
    | ExtendBot => inl $ inl tt
    | Extend a => inl $ inr a
    | ExtendTop => inr tt
    end.

  Definition sum_to_extend {A} (s:unit+A+unit) : extend A :=
    match s with
    | inl (inl tt) => ExtendBot
    | inl (inr a) => Extend a
    | inr tt => ExtendTop
    end.

  Global Instance IR_extend_to_sum_eq {A} : InjectionRespect (extend A) (unit+A+unit) extend_to_sum eq eq.
  Proof.
    constructor ; intros.
    - congruence.
    - unfold Proper,"<==" ; intros.
      destruct x,y ; simpl in * ; congruence.
  Qed.

  Global Instance IR_sum_to_extend_eq {A} : InjectionRespect (unit+A+unit) (extend A) sum_to_extend eq eq.
  Proof.
    constructor ; intros.
    - congruence.
    - unfold Proper,"<==" ; intros
      ; repeat
          match goal with
          | [ X : sum _ _ |- _ ] => destruct X
          | [ X : unit |- _ ] => destruct X
          end
      ; simpl in * ; congruence.
  Qed.

  Global Instance II_sum_to_extend_eq {A} : InjectionInverse (unit+A+unit) (extend A) sum_to_extend extend_to_sum eq.
  Proof.
    constructor ; intros
    ; repeat
        match goal with
        | [ X : sum _ _ |- _ ] => destruct X
        | [ X : unit |- _ ] => destruct X
        end
    ; simpl in * ; congruence.
  Qed.
End extend_Bijection.

Module extend_DE_Arg <: DE_Functor_Arg.
  Definition T := extend.
  Definition U A := (unit:Type)+A+unit.
  Definition to : forall {A}, T A -> U A := @extend_to_sum.
  Definition from : forall {A}, U A -> T A := @sum_to_extend.
  Definition IR_to {A} : InjectionRespect (T A) (U A) to eq eq := _.
  Definition II_from {A} : InjectionInverse (U A) (T A) from to eq := _.
  Definition _DE_FunctorI : DE_FunctorI' U.
  Proof. econstructor ; econstructor ; eauto with typeclass_instances. Defined.
End extend_DE_Arg.
Module extend_DE := DE_Functor extend_DE_Arg.
Import extend_DE.

Section Proper.
  Context {T} `{! Lte T ,! Eqv T ,! PER_WF T }.

  Global Instance IR_Extend_eqv : InjectionRespect T (extend T) Extend eqv eqv.
  Proof.
    constructor ; unfold Proper,"==>","<==" ; intros.
    - apply InjectionRespect_beta ; simpl.
      repeat apply InjectionRespect_eta ; auto.
    - apply InjectionRespect_eta in H ; simpl in H.
      repeat apply InjectionRespect_beta in H ; auto.
  Qed.

  Global Instance IR_Extend_lte : InjectionRespect T (extend T) Extend lte lte.
  Proof.
    constructor ; unfold Proper,"==>","<==" ; intros.
    - apply InjectionRespect_beta ; simpl.
      repeat apply InjectionRespect_eta ; auto.
    - apply InjectionRespect_eta in H ; simpl in H.
      repeat apply InjectionRespect_beta in H ; auto.
  Qed.
End Proper.
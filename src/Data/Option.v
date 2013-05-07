Require Import FP.CoreData.
Require Import FP.CoreClasses.
Require Import FP.Categories.
Require Import FP.Deriving.
Require Import FP.Data.Type.
Require Import FP.Data.Sum.
Require Import FP.Data.Unit.

Import CoreClassesNotation.
Import CategoriesNotation.

Arguments Some {A} _.
Arguments None {A}.

Definition option_elim {A C} (aM:option A) (z:C) (f:A -> C) : C :=
  match aM with
  | None => z
  | Some a => f a
  end.
Definition from_option {A} (a:A) (aM:option A) : A := option_elim aM a id.

Ltac destruct_option_eqv x y :=
  match goal with
  | [ e : eqv x y |- _ ] =>
      destruct x,y
      ; [ apply InjectionRespect_beta in e
        | inversion e
        | inversion e
        | idtac
        ]
  end.

Ltac fold_option_elim :=
  match goal with
  | [ |- context
         [ match ?aM with
           | None => ?z
           | Some a => (@?f a)
           end
         ]
    ] => fold (option_elim aM z f)
  end.

Section sum_Bijection.
  Context {A:Type}.

  Definition option_to_sum (aM:option A) : unit + A :=
    match aM with
    | None => inl tt
    | Some a => inr a
    end.
  Global Instance IR_option_to_sum_eq
    : InjectionRespect (option A) (unit+A) option_to_sum eq eq.
  Proof.
    constructor ; unfold Proper ; simpl in * ; intros ; try congruence.
    destruct x,y ; simpl in * ; congruence.
  Qed.

  Definition sum_to_option (aM:unit+A) : option A :=
    match aM with
    | inl tt => None
    | inr a => Some a
    end.
  Global Instance II_sum_to_option_eq
    : InjectionInverse (unit+A) (option A) sum_to_option option_to_sum eq.
  Proof.
    constructor ; intros.
    destruct x ; [ destruct u | idtac ] ; simpl in * ; auto.
  Qed.
End sum_Bijection.

Module option_DerivingEverything_Functor_Arg <: DerivingEverything_Functor_Arg.
  Definition T A := option A.
  Definition U A := (unit:Type)+A.
  Definition to {A} (x:T A) := option_to_sum x.
  Definition from {A} (x:U A) := sum_to_option x.
  Definition InjResp {A} : InjectionRespect (T A) (U A) to eq eq := _.
  Definition InjInv {A} : InjectionInverse (U A) (T A) from to eq := _.
  Definition _DerivingEverything_FunctorI : DerivingEverything_FunctorI U.
  Proof. econstructor ; eauto with typeclass_instances. Defined.
End option_DerivingEverything_Functor_Arg.

Module option_DerivingEverything_Functor :=
  DerivingEverything_Functor option_DerivingEverything_Functor_Arg.
Import option_DerivingEverything_Functor.

Section Properties.
  Context {A} `{! Eqv A }.

  Global Instance IR_Some_eqv : InjectionRespect A (option A) Some eqv eqv.
  Proof.
    constructor ; unfold Proper,"==>","<==" ; intros.
    - constructor ; auto.
    - inversion H ; auto.
  Qed.

  Global Instance None_Proper : Proper eqv None.
  Proof.
    unfold Proper,eqv ; simpl.
    eapply InjectionRespect_eta ; reflexivity.
  Qed.

  Global Instance Some_Proper : Proper eqv Some.
  Proof.
    unfold Proper ; logical_eqv_intro.
    apply InjectionRespect_eta ; auto.
  Qed.

  Context {C} `{! Eqv C }.
  Instance option_elim_respect : Proper eqv (option_elim (A:=A) (C:=C)).
  Proof.
    unfold option_elim.
    logical_eqv.
    destruct_option_eqv x y ; logical_eqv.
  Qed.
End Properties.
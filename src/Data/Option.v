Require Import FP.CoreData.
Require Import FP.CoreClasses.
Require Import FP.Categories.
Require Import FP.DerivingEverything.
Require Import FP.DerivingMonad.
Require Import FP.Data.Type.
Require Import FP.Data.Sum.
Require Import FP.Data.Unit.
Require Import FP.Data.Error.
Require Import FP.Data.ErrorMonad.

Import CoreClassesNotation.
Import CategoriesNotation.

Arguments Some {A} _.
Arguments None {A}.

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

Module option_DE_Arg <: DE_Functor_Arg.
  Definition T := option.
  Definition U A := (unit:Type)+A.
  Definition to : forall {A}, T A -> U A := @option_to_sum.
  Definition from : forall {A}, U A -> T A := @sum_to_option.
  Definition IR_to {A} : InjectionRespect (T A) (U A) to eq eq := _.
  Definition II_from {A} : InjectionInverse (U A) (T A) from to eq := _.
  Definition _DE_FunctorI : DE_FunctorI U.
  Proof. econstructor ; eauto with typeclass_instances. Defined.
End option_DE_Arg.
Module option_DE := DE_Functor option_DE_Arg.
Import option_DE.

Definition option_elim {A C} (aM:option A) (z:C) (f:A -> C) : C :=
  match aM with
  | None => z
  | Some a => f a
  end.
Definition from_option {A} (a:A) (aM:option A) : A := option_elim aM a id.
Section Proper_option_elim.
  Context {A C} `{! Eqv A ,! PER_WF A ,! Eqv C ,! PER_WF C }.

  Global Instance Proper_option_elim : Proper eqv (@option_elim A C).
  Proof.
    unfold Proper ; logical_eqv_intro.
    destruct x,y ; simpl ; inversion H ; subst ; clear H ; logical_eqv.
  Qed.
End Proper_option_elim.

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

Ltac fold_option :=
  match goal with
  | [ |- context
         [ match ?aM with
           | None => ?z
           | Some a => (@?f a)
           end
         ]
    ] => fold (option_elim aM z f)
  end.

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

Section error_Bijection.
  Definition option_to_error {A} (aM:option A) : error unit A :=
    match aM with
    | None => Failure tt
    | Some a => Success a
    end.

  Definition error_to_option {A} (aM:error unit A) : option A :=
    match aM with
    | Failure tt => None
    | Success a => Some a
    end.

  Global Instance IR_error_to_option_eqv {A} `{! Eqv A ,! PER_WF A }
    : InjectionRespect (error unit A) (option A) error_to_option eqv eqv.
  Proof.
    constructor ; unfold Proper,"==>","<==" ; intros.
    - destruct x,y ; simpl
      ; repeat
          match goal with
          | [ H : unit |- _ ] => destruct H
          end
      ; auto.
    - destruct x,y ; simpl in *
      ; repeat
          match goal with
          | [ H : unit |- _ ] => destruct H
          end
      ; auto.
    Qed.

  Global Instance II_option_to_error_eqv {A} `{! Eqv A ,! PER_WF A }
    : InjectionInverse (option A) (error unit A) option_to_error error_to_option eqv.
  Proof.
    constructor ; intros.
    destruct x ; simpl ; auto.
  Qed.

  Global Instance II_error_to_option_eqv {A} `{! Eqv A ,! PER_WF A }
    : InjectionInverse (error unit A) (option A) error_to_option option_to_error eqv.
  Proof.
    constructor ; intros.
    destruct x
    ; try
        match goal with
        | [ H : unit |- _ ] => destruct H
        end
    ; auto.
  Qed.

  Global Instance Proper_option_to_error {A} `{! Eqv A ,! PER_WF A } : Proper eqv option_to_error.
  Proof.
    unfold Proper ; logical_eqv_intro ; unfold option_to_error
    ; simpl ; repeat fold_option ; logical_eqv.
  Qed.

  Global Instance Proper_error_to_option {A} `{! Eqv A ,! PER_WF A } : Proper eqv error_to_option.
  Proof.
    unfold Proper ; logical_eqv_intro ; unfold error_to_option
    ; simpl ; repeat fold_error ; logical_eqv
    ; repeat
        match goal with
        | [ H : unit |- _ ] => destruct H
        end
    ; auto.
    constructor ; auto.
  Qed.
End error_Bijection.

Module option_DMError_Arg <: DMError_Functor_Arg.
  Definition T := option.
  Definition U := error unit.
  Definition to : forall {A}, T A -> U A := @option_to_error.
  Definition from : forall {A}, U A -> T A := @error_to_option.
  Definition _DM_FunctorI : DM_FunctorI T U.
  Proof. econstructor ; eauto with typeclass_instances. Defined.
  Definition IR_from_eqv :
    forall {A} `{! Eqv A ,! PER_WF A },
    InjectionRespect (U A) (T A) from eqv eqv := _.
  Definition II_to_from_eqv :
    forall {A} `{! Eqv A ,! PER_WF A },
    InjectionInverse (T A) (U A) to from eqv := _.
  Definition II_from_from_eqv :
    forall {A} `{! Eqv A ,! PER_WF A },
    InjectionInverse (U A) (T A) from to eqv := _.
  Definition Proper_to_eqv :
    forall {A} `{! Eqv A ,! PER_WF A },
    Proper eqv (@to A) := _.
  Definition Proper_from_eqv :
    forall {A} `{! Eqv A ,! PER_WF A },
    Proper eqv (@from A) := _.

  Definition E := unit.
  Definition _DMError_FunctorI : DMError_FunctorI unit T U.
  Proof. econstructor ; eauto with typeclass_instances. Defined.
End option_DMError_Arg.

Module option_DMError := DMError_Functor option_DMError_Arg.
Import option_DMError.

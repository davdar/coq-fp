Require Import FP.Data.Function.
Require Import FP.Data.Bool.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Ord.
Require Import FP.Relations.RelDec.
Require Import FP.Data.List.

Import FunctionNotation.
Import EqDecNotation.
Import EqvNotation.
Import OrdNotation.
Import ListNotation.
Import BoolNotation.

Section EqDec.
  Context {A} {AED:EqDec A}.

  Fixpoint list_eq_dec (xL:list A) (yL:list A) : bool :=
    match xL, yL with
    | nil, nil => true
    | x::xL', y::yL' => x =! y && list_eq_dec xL' yL'
    | _, _ => false
    end.

  Global Instance list_EqDec : EqDec (list A) := { eq_dec := list_eq_dec }.

  Context {ARDC:RelDecCorrect A eq eq_dec}.

  Global Instance list_Eq_RelDecCorrect : RelDecCorrect (list A) eq eq_dec.
  Admitted.
End EqDec.

Section Eqv.
  Context {A} {AE:Eqv A}.

  Inductive list_eqv : list A -> list A -> Prop :=
    | NilEqv : list_eqv nil nil
    | ConsEqv : forall x y xL yL, x ~= y -> list_eqv xL yL -> list_eqv (x::xL) (y::yL).

  Global Instance list_Eqv : Eqv (list A) := { eqv := list_eqv }.

  Context {AEE:EqvWF A}.

  Global Instance list_Equivalence : EqvWF (list A).
  Admitted.
End Eqv.

Section EqvDec.
  Context {A} {AED:EqvDec A}.

  Fixpoint list_eqv_dec (xL:list A) (yL:list A) : bool :=
    match xL, yL with
    | nil, nil => true
    | x::xL', y::yL' => x ~=! y && list_eqv_dec xL' yL'
    | _, _ => false
    end.

  Global Instance list_EqvDec : EqvDec (list A) := { eqv_dec := list_eqv_dec }.

  Context {AE:Eqv A} {ARDC:RelDecCorrect A eqv eqv_dec}.

  Global Instance list_Eqv_RelDecCorrect : RelDecCorrect (list A) eqv eqv_dec.
  Admitted.
End EqvDec.

Section Ord.
  Context {A} {AE:Eqv A} {AL:Ord A}.

  Inductive list_lt : list A -> list A -> Prop :=
    | NilLte : forall x xL,
        list_lt nil (x::xL)
    | HeadLte : forall x y xL yL,
        x < y -> list_lt (x::xL) (y::yL)
    | TailLte : forall x y xL yL,
        x ~= y -> list_lt xL yL -> list_lt (x::xL) (y::yL).

  Global Instance list_Ord : Ord (list A) := { lt := list_lt }.
End Ord.

Section OrdDec.
  Context {A:Type}.

  Fixpoint list_ord_dec_b (a_ord_dec:A -> A -> comparison) (xL:list A) (yL:list A) : comparison :=
    match xL, yL with
    | nil, nil => Eq
    | nil, _::_ => Lt
    | _::_, nil => Gt
    | x::xL', y::yL' =>
        match x `a_ord_dec` y with
        | Lt => Lt
        | Gt => Gt
        | Eq => list_ord_dec_b a_ord_dec xL' yL'
        end
    end.

  Context {ALD:OrdDec A}.

  Definition list_ord_dec : list A -> list A -> comparison := list_ord_dec_b ord_dec.

  Global Instance list_OrdDec : OrdDec (list A) := { ord_dec := list_ord_dec }.
End OrdDec.
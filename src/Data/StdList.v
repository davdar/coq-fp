Require Import Equivalence.

Require Import StdBool.
Require Import StdAscii.
Import BoolNotation.
Require Import Eq.
Import EqNotation.
Require Import Eqv.
Import EqvNotation.
Require Import Lte.
Import LteNotation.
Require Import RelDec.
Require Import Show.
Require Import Monoid.
Import MonoidNotation.
Require Import Morphism.
Require Import Pointed.

Module ListNotation.
  Infix "::" := cons.
End ListNotation.
Import ListNotation.

Section EqDec.
  Context {A} {AED:EqDec A}.

  Fixpoint list_eq_dec (xL:list A) (yL:list A) : bool :=
    match xL, yL with
    | nil, nil => true
    | x::xL', y::yL' => x =! y && list_eq_dec xL' yL'
    | _, _ => false
    end.

  Global Instance list_EqDec : EqDec (list A) := { eq_dec := list_eq_dec }.

  Context {ARDC:RelDecCorrect (T:=A) eq_dec eq}.

  Global Instance list_Eq_RelDecCorrect : RelDecCorrect (T:=list A) eq_dec eq.
  Admitted.
End EqDec.

Section Eqv.
  Context {A} {AE:Eqv A}.

  Inductive list_eqv : list A -> list A -> Prop :=
    | NilEqv : list_eqv nil nil
    | ConsEqv : forall x y xL yL, x ~= y -> list_eqv xL yL -> list_eqv (x::xL) (y::yL).

  Global Instance list_Eqv : Eqv (list A) := { eqv := list_eqv }.

  Context {AEE:Equivalence (A:=A) eqv}.

  Global Instance list_Equivalence : Equivalence (A:=list A) eqv.
  Admitted.
End Eqv.

Section EqvDec.
  Context {A B} {AED:EqvDec A} {BED:EqvDec B}.

  Fixpoint list_eqv_dec (xL:list A) (yL:list A) : bool :=
    match xL, yL with
    | nil, nil => true
    | x::xL', y::yL' => x ~=! y && list_eqv_dec xL' yL'
    | _, _ => false
    end.

  Global Instance list_EqvDec : EqvDec (list A) := { eqv_dec := list_eqv_dec }.

  Context {AE:Eqv A} {ARDC:RelDecCorrect (T:=A) eqv_dec eqv}.

  Global Instance list_Eqv_RelDecCorrect : RelDecCorrect (T:=list A) eqv_dec eqv.
  Admitted.
End EqvDec.

Section Lte.
  Context {A} {AL:Lte A}.

  Inductive list_lte : list A -> list A -> Prop :=
    | NilLte : forall x,
        list_lte nil x
    | HeadLte : forall x y xL yL,
        x '< y -> list_lte (x::xL) (y::yL)
    | TailLte : forall x y xL yL,
        x '<=> y -> list_lte xL yL -> list_lte (x::xL) (y::yL).

  Global Instance list_Lte : Lte (list A) := { lte := list_lte }.

  Context {ALPO:PreOrder (A:=A) lte}.

  Global Instance list_PreOrder : PreOrder (A:=list A) lte.
  Admitted.
End Lte.

Section LteDec.
  Context {A} {ALD:LteDec A}.

  Fixpoint list_lte_dec (xL:list A) (yL:list A) : bool :=
    match xL, yL with
    | nil, _ => true
    | x::xL', y::yL' =>
        if x '<! y then true
        else if x '>! y then false
        else list_lte_dec xL' yL'
    | _, _ => false
    end.

  Global Instance list_LteDec : LteDec (list A) := { lte_dec := list_lte_dec }.

  Context {AL:Lte A} {ARDC:RelDecCorrect (T:=A) lte_dec lte}.

  Global Instance list_Lte_RelDecCorrect : RelDecCorrect (T:=list A) lte_dec lte.
  Admitted.
End LteDec.

Section Show.
  Context {A} {AS:Show A}.

  Section list_show.
    Variable (R:Type) (SR:ShowResult R).

    Fixpoint list_show_inner (xL:list A) :=
      match xL with
      | nil => top
      | x::xL' =>
             rawshow_string "; "
          ** show x
          ** list_show_inner xL'
      end.
          
    Definition list_show (xL:list A) : R :=
      match xL with
      | nil => rawshow_string "[]"
      | x::nil =>
             rawshow_char "["%char
          ** show x
          ** rawshow_char "]"%char
      | x1::x2::xL' =>
             rawshow_char "["%char
          ** show x1
          ** list_show_inner (x2::xL)
          ** rawshow_char "]"%char
      end.
  End list_show.

  Global Instance list_Show : Show (list A) := { show := list_show }.
End Show.

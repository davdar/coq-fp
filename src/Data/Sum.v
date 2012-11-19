Require Export Data.SumPre.

Require Import Data.AsciiPre.
Require Import Data.BoolPre.
Require Import Data.FunctionPre.
Require Import Data.StringPre.

Require Import Relations.RelDec.
Require Import Structures.EqDec.
Require Import Structures.Eqv.
Require Import Structures.Monad.
Require Import Structures.MonadError.
Require Import Structures.MonadFix.
Require Import Structures.MonadPlus.
Require Import Structures.Monoid.
Require Import Structures.Ord.
Require Import Structures.RelationClasses.
Require Import Structures.Show.

Import CharNotation.
Import EqDecNotation.
Import EqvNotation.
Import FunctionNotation.
Import MonadNotation.
Import MonoidNotation.
Import OrdNotation.
Import StringNotation.

Local Infix "+" := sum.

Section EqDec.
  Context {A B} {AED:EqDec A} {BED:EqDec B}.

  Definition sum_eq_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 '=! a2
    | inr b1, inr b2 => b1 '=! b2
    | _, _ => false
    end.

  Global Instance sum_EqDec : EqDec (A+B) := { eq_dec := sum_eq_dec }.

  Context {ARDC:RelDecCorrect (T:=A) eq_dec eq}.
  Context {BRDC:RelDecCorrect (T:=B) eq_dec eq}.

  Global Instance sum_Eq_RelDecCorrect : RelDecCorrect (T:=A+B) eq_dec eq.
  Admitted.
End EqDec.

Section Eqv.
  Context {A B} {AE:Eqv A} {BE:Eqv B}.

  Inductive sum_eqv : A+B -> A+B -> Prop :=
    | InlSumEqv : forall a1 a2 , a1 '~= a2 -> sum_eqv (inl a1) (inl a2)
    | InrSumEqv : forall b1 b2, b1 '~= b2 -> sum_eqv (inr b1) (inr b2).

  Global Instance sum_Eqv : Eqv (A+B) := { eqv := sum_eqv }.

  Context {AEE:Equivalence (A:=A) eqv} {BEE:Equivalence (A:=B) eqv}.

  Global Instance sum_Equivalence : Equivalence (A:=A+B) eqv.
  Admitted.
End Eqv.

Section EqvDec.
  Context {A B} {AED:EqvDec A} {BED:EqvDec B}.

  Definition sum_eqv_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 '~=! a2
    | inr b1, inr b2 => b1 '~=! b2
    | _, _ => false
    end.

  Global Instance sum_EqvDec : EqvDec (A+B) := { eqv_dec := sum_eqv_dec }.

  Context {AE:Eqv A} {ARDC:RelDecCorrect (T:=A) eqv_dec eqv}.
  Context {BE:Eqv B} {BRDC:RelDecCorrect (T:=B) eqv_dec eqv}.

  Global Instance sum_Eqv_RelDecCorrect : RelDecCorrect (T:=A+B) eqv_dec eqv.
  Admitted.
End EqvDec.

Section Ord.
  Context {A B} {AL:Ord A} {BL:Ord B}.

  Inductive sum_lt : A+B -> A+B -> Prop :=
    | InlSumLte : forall a1 a2, a1 '< a2 -> sum_lt (inl a1) (inl a2)
    | InrSumLte : forall b1 b2, b1 '< b2 -> sum_lt (inr b1) (inr b2)
    | MisSumLte : forall a1 b2, sum_lt (inl a1) (inr b2).
      
  Global Instance sum_Ord : Ord (A+B) := { lt := sum_lt }.
End Ord.

Section OrdDec.
  Context {A B:Type}.

  Definition sum_ord_dec_b (a_ord_dec:A -> A -> comparison) (b_ord_dec:B -> B -> comparison)
      (ab1:A+B) (ab2:A+B) : comparison :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 `a_ord_dec` a2
    | inr b1, inr b2 => b1 `b_ord_dec` b2
    | inl _, inr _ => Lt
    | inr _, inl _ => Gt
    end.

  Context {ALD:OrdDec A} {BLD:OrdDec B}.

  Definition sum_ord_dec : A+B -> A+B -> comparison := sum_ord_dec_b ord_dec ord_dec.

  Global Instance sum_OrdDec : OrdDec (A+B) := { ord_dec := sum_ord_dec }.
End OrdDec.

Section Show.
  Context {A B} {AS:Show A} {BS:Show B}.

  Section sum_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition sum_show (ab:A+B) : R :=
      let (tag, payload) :=
        match ab with
        | inl a => ("inl", show a)
        | inr b => ("inr", show b)
        end
      in raw_char "("%char
      ** raw_string tag
      ** raw_char " "%char
      ** payload
      ** raw_char ")"%char.
  End sum_show.

  Global Instance sum_Show : Show (A+B) := { show := sum_show }.
End Show.

Section Type_Monoid.
  Definition sum_Type_Monoid : Monoid Type :=
    {| Monoid_Semigroup := {| gtimes := sum |}
     ; gunit := (Empty_set:Type)
    |}.
End Type_Monoid.

Section sum_Monad.
  Context {A:Type}.
  Definition sum_ret {B} : B -> A+B := inr.
  Definition sum_bind {B C} (bM:A+B) (f:B -> A+C) : A+C :=
    match bM with
    | inl x => inl x
    | inr y => f y
    end.
  Global Instance sum_Monad : Monad (sum A) :=
    { ret := @sum_ret
    ; bind := @sum_bind
    }.
End sum_Monad.

Section sum_MonadError.
  Context {A:Type}.
  Definition sum_throw {B} : A -> A+B := inl.
  Definition sum_catch {B} (bM:A+B) (h:A -> A+B) : A+B :=
    match bM with
    | inl x => h x
    | inr y => inr y
    end.
  Global Instance sum_MonadError : MonadError A (sum A) :=
    { throw := @sum_throw
    ; catch := @sum_catch
    }.
End sum_MonadError.
       
Inductive sum_t A m B := SumT { un_sum_t : m (A+B) }.
Arguments SumT {A m B} un_sum_t.
Arguments un_sum_t {A m B} _.

Definition run_sum_t {A m B} : sum_t A m B -> m (A+B) := un_sum_t.

Section sum_t_Monad.
  Context {A:Type} {m} {M:Monad m}.

  Definition sum_t_ret {B} : B -> sum_t A m B := SumT <.> ret <.> inr.
  Definition sum_t_bind {B C} (bMM:sum_t A m B) (f:B -> sum_t A m C) : sum_t A m C :=
    SumT $ begin
      ab <- un_sum_t bMM ;;
      match ab with
      | inl x => ret $ inl x
      | inr y => un_sum_t $ f y
      end
    end.
  Global Instance sum_t_Monad : Monad (sum_t A m) :=
    { ret := @sum_t_ret
    ; bind := @sum_t_bind
    }.
End sum_t_Monad.

Section sum_t_MonadPlus.
  Context {A} {aM:Monoid A} {m} {mM:Monad m}.

  Definition sum_t_mzero {B} : sum_t A m B := SumT $ ret $ inl gunit.
  Definition sum_t_mplus {B C} (bMM:sum_t A m B) (cMM:sum_t A m C) : sum_t A m (B+C) :=
    SumT $ begin
      ab <- un_sum_t bMM ;;
      match ab with
      | inl e1 =>
          ac <- un_sum_t cMM ;;
          match ac with
          | inl e2 => ret $ inl $ e1 ** e2
          | inr c => ret $ inr $ inr c
          end
      | inr b => ret $ inr $ inl b
      end
    end.
  Global Instance sum_t_MonadPlus : MonadPlus (sum_t A m) :=
    { mzero := @sum_t_mzero
    ; mplus := @sum_t_mplus
    }.
      
    
End sum_t_MonadPlus.

Section sum_t_MonadError.
  Context {A:Type} {m} {M:Monad m}.

  Definition sum_t_throw {B} : A -> sum_t A m B := SumT <.> ret <.> inl.
  Definition sum_t_catch {B} (bMM:sum_t A m B) (h:A -> sum_t A m B) : sum_t A m B :=
    SumT $ begin
      ab <-  un_sum_t bMM ;;
      match ab with
      | inl x => un_sum_t $ h x
      | inr y => ret $ inr y
      end
    end.
  Global Instance sum_t_MonadError : MonadError A (sum_t A m) :=
    { throw := @sum_t_throw
    ; catch := @sum_t_catch
    }.
End sum_t_MonadError.

Section sum_t_MonadFix.
  Context {A:Type} {m} {M:Monad m} {MF:MonadFix m}.

  Definition sum_t_mfix {B C} (ff:(B -> sum_t A m C) -> B -> sum_t A m C) (b:B) : sum_t A m C :=
    let ff' (f':B -> m (A+C)) :=
      let f := SumT <.> f' in
      un_sum_t <.> ff f
    in
    SumT $ mfix ff' b.
  Global Instance sum_t_MonadFix : MonadFix (sum_t A m) :=
    { mfix := @sum_t_mfix }.
End sum_t_MonadFix.
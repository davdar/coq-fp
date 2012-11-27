Require Export FP.Data.SumPre.

Require Import FP.Data.AsciiPre.
Require Import FP.Data.BoolPre.
Require Import FP.Data.FunctionPre.
Require Import FP.Data.StringPre.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadError.
Require Import FP.Structures.MonadFix.
Require Import FP.Structures.MonadPlus.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Ord.
Require Import FP.Structures.RelationClasses.
Require Import FP.Structures.Show.
Require Import FP.Structures.Injection.
Require Import FP.Data.Identity.

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

Inductive sum_t A m B := SumT { un_sum_t : m (A+B) }.
Arguments SumT {A m B} un_sum_t.
Arguments un_sum_t {A m B} _.

Section sum_t_Monad.
  Context {A:Type} {m} {M:Monad m}.

  Definition run_sum_t {B} : sum_t A m B -> m (A+B) := un_sum_t.

  Section Monad.
    Definition sum_t_ret {B} : B -> sum_t A m B := SumT <.> ret <.> inr.
    Definition sum_t_bind {B C}
        (bMM:sum_t A m B) (f:B -> sum_t A m C) : sum_t A m C :=
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
  End Monad.

  Section MonadError.
    Definition sum_t_throw {B} : A -> sum_t A m B := SumT <.> ret <.> inl.
    Definition sum_t_catch {B}
        (bMM:sum_t A m B) (h:A -> sum_t A m B) : sum_t A m B :=
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
  End MonadError.

  Section MonadPlus.
    Context {AM:Monoid A}.

    Definition sum_t_mzero {B} : sum_t A m B := SumT $ ret $ inl gunit.
    Definition sum_t_mplus {B C} (bMM:sum_t A m B) (cMM:sum_t A m C)
        : sum_t A m (B+C) :=
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
  End MonadPlus.

  Section MonadFix.
    Context {MF:MonadFix m}.

    Definition sum_t_mfix {B C}
        (ff:(B -> sum_t A m C) -> B -> sum_t A m C) (b:B) : sum_t A m C :=
      let ff' (f':B -> m (A+C)) :=
        let f := SumT <.> f' in
        un_sum_t <.> ff f
      in
      SumT $ mfix ff' b.
    Global Instance sum_t_MonadFix : MonadFix (sum_t A m) :=
      { mfix := @sum_t_mfix }.
  End MonadFix.
End sum_t_Monad.

Instance sum_sum_t_FunctorInjection {A}
    : FunctorInjection (sum A) (sum_t A identity) :=
  { finject := fun _ => SumT <.> Identity }.
Instance sum_t_sum_FunctorInjection {A}
    : FunctorInjection (sum_t A identity) (sum A) :=
  { finject := fun _ => run_identity <.> run_sum_t }.
Instance sum_Monad {A} : Monad (sum A) := iso_Monad (sum_t A identity).
Instance sum_MonadPlus {A} {AM:Monoid A} : MonadPlus (sum A) :=
  iso_MonadPlus (sum_t A identity).
Instance sum_MonadError {A} : MonadError A (sum A) :=
  iso_MonadError (sum_t A identity).
  
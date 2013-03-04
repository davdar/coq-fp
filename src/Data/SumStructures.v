Require Import FP.Data.Sum.
Require Import FP.Data.Ascii.
Require Import FP.Data.Bool.
Require Import FP.Data.String.
Require Import FP.Data.Function.
Require Import FP.Data.Type.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadError.
Require Import FP.Structures.FUnit.
Require Import FP.Structures.MonadFix.
Require Import FP.Structures.MonadPlus.
Require Import FP.Structures.MonadDeriving.
Require Import FP.Structures.FUnitDeriving.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Ord.
Require Import FP.Structures.Show.
Require Import FP.Structures.Injection.
Require Import FP.Data.Identity.
Require Import FP.Relations.Function.
Require Import FP.Relations.Setoid.

Import AdditiveNotation.
Import ProperNotation.
Import CharNotation.
Import EqDecNotation.
Import EqvNotation.
Import FunctionNotation.
Import MonadNotation.
Import MonoidNotation.
Import OrdNotation.
Import StringNotation.
Import LatticeNotation.

Section sum_t_Monad.
  Context {A:Type} {m} {M:Monad m}.

  Definition run_sum_t {B} : sum_t A m B -> m (A+B) := un_sum_t.

  Section Monad.
    Definition sum_t_funit {B} : B -> sum_t A m B := SumT '.' ret '.' inr.
    Global Instance sum_t_FUnit : FUnit (sum_t A m) :=
      { funit := @sum_t_funit }.

    Definition sum_t_bind {B C} (bMM:sum_t A m B) (f:B -> sum_t A m C) : sum_t A m C :=
      SumT $ begin
        ab <- un_sum_t bMM ;;
        match ab with
        | inl x => ret $ inl x
        | inr y => un_sum_t $ f y
        end
      end.
    Global Instance sum_t_Monad : MBind (sum_t A m) :=
      { bind := @sum_t_bind }.
  End Monad.

  Section MonadError.
    Definition sum_t_throw {B} : A -> sum_t A m B := SumT '.' ret '.' inl.
    Definition sum_t_catch {B}
        (bMM:sum_t A m B) (h:A -> sum_t A m B) : sum_t A m B :=
      SumT $ begin
        ab <-  un_sum_t bMM ;;
        match ab with
        | inl x => un_sum_t $ h x
        | inr y => ret $ inr y
        end
      end.
    Global Instance sum_t_MonadError : MError A (sum_t A m) :=
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
    (*
    Global Instance sum_t_MonadPlus : MonadPlus (sum_t A m) :=
      { mzero := @sum_t_mzero
      ; mplus := @sum_t_mplus
      }.
*)
  End MonadPlus.

  Section MonadFix.
    Context {MF:MFix m}.

    Definition sum_t_mfix {B C}
        (ff:(B -> sum_t A m C) -> B -> sum_t A m C) (b:B) : sum_t A m C :=
      let ff' (f':B -> m (A+C)) :=
        let f := SumT '.' f' in
        un_sum_t '.' ff f
      in
      SumT $ mfix ff' b.
    Global Instance sum_t_MonadFix : MFix (sum_t A m) :=
      { mfix := @sum_t_mfix }.
  End MonadFix.
End sum_t_Monad.

Instance sum_sum_t_FunctorInjection {A} : HasFunctorInjection (sum A) (sum_t A identity) :=
  { finject := fun _ => SumT '.' Identity }.
Instance sum_t_sum_FunctorInjection {A} : HasFunctorInjection (sum_t A identity) (sum A) :=
  { finject := fun _ => run_identity '.' run_sum_t }.

Instance sum_FUnit {A} : FUnit (sum A) := Deriving_FUnit (sum_t A identity).
Instance sum_MBind {A} : MBind (sum A) := Deriving_MBind (sum_t A identity).
(*
Instance sum_MonadPlus {A} {AM:Monoid A} : MonadPlus (sum A) :=
  iso_MonadPlus (sum_t A identity).
Instance sum_MonadError {A} : MonadError A (sum A) :=
  iso_MonadError (sum_t A identity).
*)
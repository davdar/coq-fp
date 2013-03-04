Require EqNat.
Require Peano.
Require Compare_dec.

Require Import FP.Data.Ascii.
Require Import FP.Data.Function.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.Additive.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Multiplicative.
Require Import FP.Structures.Ord.
Require Import FP.Structures.Show.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Iterable.
Require Import FP.Structures.Peano.

Import CharNotation.
Import MonoidNotation.
Import FunctionNotation.
Import ComonadNotation.
Import OrdNotation.

Module NatNotation.
  Delimit Scope nat_scope with nat.
End NatNotation.

Section EqDec.
  Global Instance nat_EqDec : EqDec nat := { eq_dec := EqNat.beq_nat }.
  Global Instance nat_Eq_RelDecCorrect : RelDecCorrect nat eq eq_dec.
  Proof. constructor ; apply EqNat.beq_nat_true_iff. Qed.
End EqDec.

Section Eqv.
  Global Instance nat_Eqv : Eqv nat := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance nat_EqvDec : EqvDec nat := { eqv_dec := eq_dec }.
  Global Instance nat_Eqv_RelDecCorrect : RelDecCorrect nat eqv eqv_dec.
  Proof. apply nat_Eq_RelDecCorrect. Qed.
End EqvDec.

Section Ord.
  Global Instance nat_Ord : Ord nat := { lt := Peano.lt }.
End Ord.

Section OrdDec.
  Global Instance nat_OrdDec : OrdDec nat := { ord_dec := Compare_dec.nat_compare  }.
End OrdDec.

Section Lattice.
  Global Instance nat_Lattice : Lattice nat :=
    { lmeet := Peano.min
    ; ljoin := Peano.max
    }.
End Lattice.

Section Show.
  Require Coq.Program.Wf.
  Require Omega.

  Section nat_show.

    Variable (R:Type) (SR:ShowResult R).

    Definition digit2char (n:nat) : Ascii.ascii :=
      match n with
        | 0 => "0"%char
        | 1 => "1"%char
        | 2 => "2"%char
        | 3 => "3"%char
        | 4 => "4"%char
        | 5 => "5"%char
        | 6 => "6"%char
        | 7 => "7"%char
        | 8 => "8"%char
        | _ => "9"%char
      end.

    Program Fixpoint nat_show (n:nat) {measure n} : R :=
      if Compare_dec.le_gt_dec n 9 then
        raw_char (digit2char n)
      else
        let n' := NPeano.div n 10 in
        nat_show n' ** raw_char (digit2char (n - 10 * n')).
    Next Obligation.
      assert (NPeano.div n 10 < n) ; eauto.
      eapply NPeano.Nat.div_lt ; omega.
    Defined.
  End nat_show.

  Global Instance nat_Show : Show nat := { show := nat_show }.
End Show.

Section Additive.
  Definition nat_additive_DivMonoid : DivMonoid nat :=
    {| div_monoid_times := Peano.plus
     ; div_monoid_unit := O
     ; div_monoid_div := Peano.minus
    |}.
  Global Instance nat_MinusAdditive : MinusAdditive nat :=
    { minus_additive_DivMonoid := nat_additive_DivMonoid }.
End Additive.
Section Multiplicative.
  Definition nat_multiplicative_DivMonoid : DivMonoid nat :=
    {| div_monoid_times := Peano.mult
     ; div_monoid_unit := S O
     ; div_monoid_div := NPeano.div
    |}.
  Global Instance nat_DivMultiplicative : DivMultiplicative nat :=
    { div_multiplicative_DivMonoid := nat_multiplicative_DivMonoid }.
End Multiplicative.

Fixpoint nat_cofold {m} {C:Comonad m} {A} (f:nat -> m A -> A) (aM:m A) (n:nat) : A :=
  match n with
  | O => f O aM
  | S n =>
      let aM := codo aM => nat_cofold f aM n in
      f (S n) aM
  end.
Instance nat_Foldable : Foldable nat nat :=
  { cofold := @nat_cofold }.

Fixpoint nat_coiter {m} {C:Comonad m} {A} (f:m A -> nat -> A) (aM:m A) (n:nat) : A :=
  match n with
  | O => f aM O
  | S n =>
      let aM := codo aM => f aM (S n) in
      nat_coiter f aM n
  end.
Instance nat_Iterable : Iterable nat nat :=
  { coiter := @nat_coiter }.

Fixpoint nat_coloopr {m} {M:Comonad m} {A} (f:m A -> A) (aM:m A) (n:nat) : A :=
  match n with
  | O => coret aM
  | S n =>
      let aM := codo aM => nat_coloopr f aM n in
      f aM
  end.
Fixpoint nat_coloopl {m} {M:Comonad m} {A} (f:m A -> A) (aM:m A) (n:nat) : A :=
  match n with
  | O => coret aM
  | S n =>
      let aM := codo aM => f aM in
      nat_coloopl f aM n
  end.
Instance nat_Peano : Peano nat :=
  { pzero := O
  ; psucc := S
  ; coloopr := @nat_coloopr
  ; coloopl := @nat_coloopl
  }.
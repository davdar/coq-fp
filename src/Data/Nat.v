Require EqNat.
Require Peano.
Require Compare_dec.

Require Import Data.AsciiPre.
Require Import Data.FunctionPre.

Require Import Relations.RelDec.
Require Import Structures.Additive.
Require Import Structures.EqDec.
Require Import Structures.Eqv.
Require Import Structures.Lattice.
Require Import Structures.Monoid.
Require Import Structures.Multiplicative.
Require Import Structures.Ord.
Require Import Structures.RelationClasses.
Require Import Structures.Show.
Require Import Structures.Comonad.
Require Import Structures.Foldable.
Require Import Structures.Functor.
Require Import Structures.Peano.

Import CharNotation.
Import MonoidNotation.
Import FunctionNotation.
Import ComonadNotation.
Import OrdNotation.

Section EqDec.
  Global Instance nat_EqDec : EqDec nat := { eq_dec := EqNat.beq_nat }.
  Global Instance nat_Eq_RelDecCorrect : RelDecCorrect (T:=nat) eq_dec eq.
  Proof. constructor ; apply EqNat.beq_nat_true_iff. Qed.
End EqDec.

Section Eqv.
  Global Instance nat_Eqv : Eqv nat := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance nat_EqvDec : EqvDec nat := { eqv_dec := eq_dec }.
  Global Instance nat_Eqv_RelDecCorrect : RelDecCorrect (T:=nat) eqv_dec eqv.
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
    { meet := Peano.min
    ; join := Peano.max
    }.
End Lattice.

Section Show.
  Require Import Coq.Program.Wf.
  Require Import Omega.

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
  Definition nat_additive_Monoid : Monoid nat :=
    {| Monoid_Semigroup := {| gtimes := Peano.plus |}
     ; gunit := O
    |}.
  Global Instance nat_Additive : Additive nat :=
    { Additive_Monoid := nat_additive_Monoid }.
End Additive.
Section Multiplicative.
  Definition nat_multiplicative_Monoid : Monoid nat :=
    {| Monoid_Semigroup := {| gtimes := Peano.mult |}
     ; gunit := S O
    |}.
  Global Instance nat_Multiplicative : Multiplicative nat :=
    { Multiplicative_Monoid := nat_multiplicative_Monoid }.
End Multiplicative.

Fixpoint nat_cofoldr {m} {C:Comonad m} {A} (f:nat -> m A -> A) (aM:m A) (n:nat) : A :=
  match n with
  | O => f O aM
  | S n =>
      let aM := codo aM => nat_cofoldr f aM n in
      f (S n) aM
  end.
Instance nat_FoldableR : FoldableR nat nat :=
  { cofoldr := @nat_cofoldr }.

Fixpoint nat_cofoldl {m} {C:Comonad m} {A} (f:m A -> nat -> A) (aM:m A) (n:nat) : A :=
  match n with
  | O => f aM O
  | S n =>
      let aM := codo aM => f aM (S n) in
      nat_cofoldl f aM n
  end.
Instance nat_FoldableL : FoldableL nat nat :=
  { cofoldl := @nat_cofoldl }.

Fixpoint nat_coiterr {m} {M:Comonad m} {A} (f:m A -> A) (aM:m A) (n:nat) : A :=
  match n with
  | O => coret aM
  | S n =>
      let aM := codo aM => nat_coiterr f aM n in
      f aM
  end.
Instance nat_PeanoR : PeanoR nat :=
  { coiterr := @nat_coiterr }. 

Fixpoint nat_coiterl {m} {M:Comonad m} {A} (f:m A -> A) (aM:m A) (n:nat) : A :=
  match n with
  | O => coret aM
  | S n =>
      let aM := codo aM => f aM in
      nat_coiterl f aM n
  end.
Instance nat_PeanoL : PeanoL nat :=
  { coiterl := @nat_coiterl }.
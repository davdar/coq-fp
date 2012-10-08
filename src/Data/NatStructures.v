Require Export Data.Nat.

Require Import Data.Ascii.
Require Import Relations.RelDec.
Require Import Structures.EqDec.
Require Import Structures.Eqv.
Require Import Structures.Lte.
Require Import Structures.Monoid.
Require Import Structures.RelationClasses.
Require Import Structures.Show.

Import MonoidNotation.

Section EqDec.
  Global Instance nat_EqDec : EqDec nat := { eq_dec := beq_nat }.
  Global Instance nat_Eq_RelDecCorrect : RelDecCorrect (T:=nat) eq_dec eq.
  Proof. constructor ; apply beq_nat_true_iff. Qed.
End EqDec.

Section Eqv.
  Global Instance nat_Eqv : Eqv nat := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance nat_EqvDec : EqvDec nat := { eqv_dec := beq_nat }.
  Global Instance nat_Eqv_RelDecCorrect : RelDecCorrect (T:=nat) eqv_dec eqv.
  Proof. apply nat_Eq_RelDecCorrect. Qed.
End EqvDec.

Section Lte.
  Global Instance nat_Lte : Lte nat := { lte := Peano.le }.
  Global Instance nat_PreOrder : PreOrder (A:=nat) lte.
  Admitted.
End Lte.

Section LteDec.
  Global Instance nat_LteDec : LteDec nat := { lte_dec := Compare_dec.leb  }.
  Global Instance nat_Lte_RelDecCorrect : RelDecCorrect (T:=nat) lte_dec lte.
  Admitted.
End LteDec.

Section Show.
  Require Import Coq.Program.Wf.
  Require Import Omega.

  Section nat_show.

    Variable (R:Type) (SR:ShowResult R).

    Definition digit2char (n:nat) : ascii :=
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
        rawshow_char (digit2char n)
      else
        let n' := NPeano.div n 10 in
        nat_show n' ** rawshow_char (digit2char (n - 10 * n')).
    Next Obligation.
      assert (NPeano.div n 10 < n) ; eauto.
      eapply NPeano.Nat.div_lt ; omega.
    Defined.
  End nat_show.

  Global Instance nat_Show : Show nat := { show := nat_show }.
End Show.
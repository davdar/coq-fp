Require Import Data.StringPre.

Require Import FP.Data.Function.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Ord.
Require Import FP.Structures.RelationClasses.
Require Import FP.Structures.Show.
Require Import FP.Relations.Setoid.

Import StringNotation.

Section EqDec.
  Fixpoint unit_eq_dec (_x:unit) (_y:unit) : bool := true.
  Global Instance unit_EqDec : EqDec unit := { eq_dec := unit_eq_dec }.
  Global Instance unit_Eq_RelDecCorrect : RelDecCorrect (T:=unit) eq_dec eq.
    constructor ; destruct x ; destruct y ; simpl ; constructor ; auto. Qed.
End EqDec.

Section Eqv.
  Global Instance unit_Eqv : Eqv unit := { eqv := eq }.
End Eqv.

Section EqvWF.
  Global Instance unit_EqvWF : EqvWF unit.
    constructor ; constructor ;
      [ unfold Reflexive | unfold Symmetric | unfold Transitive ] ;
      intros ;
      [ apply reflexivity | apply symmetry | eapply transitivity ] ; eauto.
    Qed.
End EqvWF.

Section EqvDec.
  Global Instance unit_EqvDec : EqvDec unit := { eqv_dec := unit_eq_dec }.
  Global Instance unit_Eqv_RelDecCorrect : RelDecCorrect (T:=unit) eqv_dec eqv.
    apply unit_Eq_RelDecCorrect. Qed.
End EqvDec.

Section Ord.
  Definition unit_lt : unit -> unit -> Prop := const2 False.
  Global Instance unit_Ord : Ord unit := { lt := unit_lt }.
End Ord.

Section OrdWF.
  Global Instance unit_OrdWF : OrdWF unit.
    constructor ; eauto with typeclass_instances.
    unfold Irreflexive ; unfold Reflexive ; unfold complement ; intros.
      compute in H ; destruct H.
    unfold Proper ; unfold "==>" ; intros ; constructor ; intros.
      rewrite <- H ; rewrite <- H0 ; auto.
      rewrite H ; rewrite H0 ; auto.
    Qed.
End OrdWF.

Section OrdDec.
  Definition unit_ord_dec : unit -> unit -> comparison := const2 Eq.
  Global Instance unit_OrdDec : OrdDec unit := { ord_dec := unit_ord_dec }.
  Global Instance unit_OrdDecCorrect : OrdDecCorrect unit.
    constructor ; intros ; constructor ; intros.
    destruct x,y ; reflexivity.
    compute ; reflexivity.
    compute in H ; congruence.
    compute in H ; destruct H.
    compute in H ; congruence.
    compute in H ; destruct H.
    Qed.
End OrdDec.

Section Show.
  Section unit_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition unit_show (_x:unit) : R := raw_string "tt".
  End unit_show.

  Global Instance unit_Show : Show unit := { show := unit_show }.
End Show.
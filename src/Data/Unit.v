Require Import Data.StringPre.

Require Import FP.Data.Function.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Ord.
Require Import FP.Structures.Show.
Require Import FP.Relations.Setoid.

Import StringNotation.

Section EqDec.
  Fixpoint unit_eq_dec (_x:unit) (_y:unit) : bool := true.
  Global Instance unit_EqDec : EqDec unit := { eq_dec := unit_eq_dec }.
  Global Instance unit_Eq_RelDecCorrect : RelDecCorrect unit eq eq_dec.
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
  Global Instance unit_Eqv_RelDecCorrect : RelDecCorrect unit eqv eqv_dec.
    apply unit_Eq_RelDecCorrect. Qed.
End EqvDec.

Section Ord.
  Definition unit_lt : unit -> unit -> Prop := const2 False.
  Global Instance unit_Ord : Ord unit := { lt := unit_lt }.
End Ord.

Section OrdWF.
  Global Instance unit_OrdWF : OrdWF unit.
  Proof. constructor ; eauto with typeclass_instances.
    unfold Irreflexive, Reflexive, complement ; simpl ; intros.
      destruct x ; inversion H.
    unfold Proper ; simpl ; intros.
      destruct x,x0 ; inversion H1.
  Qed.
End OrdWF.

Section OrdDec.
  Definition unit_ord_dec : unit -> unit -> comparison := const2 Eq.
  Global Instance unit_OrdDec : OrdDec unit := { ord_dec := unit_ord_dec }.
  Global Instance unit_OrdDecCorrect : OrdDecCorrect unit.
  Proof. constructor ; intros ; destruct x,y ;
      unfold eqv in * ; unfold lt in * ; simpl in *.
    reflexivity.
    contradiction.
    contradiction.
    reflexivity.
    compute in H ; discriminate H.
    compute in H ; discriminate H.
  Qed.
End OrdDec.

Section Lattice.
  Definition unit_meet : unit -> unit -> unit := const2 tt.
  Definition unit_join : unit -> unit -> unit := const2 tt.

  Global Instance unit_lattice : Lattice unit :=
    { lmeet := unit_meet
    ; ljoin := unit_join
    }.

  Global Instance unit_LatticeWF : LatticeWF unit.
  Proof. constructor ; eauto with typeclass_instances ; intros ; constructor ;
      destruct t1, t2 ; right ; compute ; auto.
  Qed.
End Lattice.

Section Show.
  Section unit_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition unit_show (_x:unit) : R := raw_string "tt".
  End unit_show.

  Global Instance unit_Show : Show unit := { show := unit_show }.
End Show.
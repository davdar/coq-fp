Require Import FP.CoreClasses.
Require Import FP.CoreData.

Import CoreDataNotation.

Section EqDec.
  Definition unit_eq_dec : unit -> unit -> bool := const2 true.
  Global Instance unit_EqDec : EqDec unit := { eq_dec := unit_eq_dec }.
  Global Instance unit_Eq_RDC : Eq_RDC unit.
  Proof. repeat constructor ; destruct x ; destruct y ; simpl ; constructor ; auto. Qed.
End EqDec.

Section Eqv.
  Global Instance unit_Eqv : Eqv unit := { eqv := eq }.
  Section PER_WF.
    Global Instance unit_PER_WF : PER_WF unit.
    Proof.
      constructor ; constructor ;
        [ unfold Symmetric | unfold Transitive ] ;
        intros ;
        [ apply symmetry | eapply transitivity ] ; eauto.
    Qed.
  End PER_WF.
  Section ER_WF.
    Global Instance unit_ER_WF : ER_WF unit.
    Proof.
      constructor ; constructor ;
        [ unfold Reflexive | unfold Symmetric | unfold Transitive ] ;
        intros ;
        [ apply reflexivity | apply symmetry | eapply transitivity ] ; eauto.
    Qed.
  End ER_WF.
End Eqv.

Section EqvDec.
  Global Instance unit_EqvDec : EqvDec unit := { eqv_dec := unit_eq_dec }.
  Global Instance unit_Eqv_RDC : Eqv_RDC unit.
  Proof. constructor. apply unit_Eq_RDC. Qed.
End EqvDec.

Section PreOrd.
  Global Instance unit_Lte : Lte unit := { lte := eq }.
  Global Instance unit_PreOrd : PreOrd unit.
  Proof.
    constructor ; [ unfold Reflexive | unfold Transitive ]
    ; intros ; [ reflexivity | transitivity y ] ; auto.
  Qed.
  Global Instance unit_LteDec : LteDec unit := { lte_dec := unit_eq_dec }.
  Global Instance unit_Lte_RDC : Lte_RDC unit.
  Proof.
    repeat constructor ; intros ; simpl ; auto.
    destruct x,y ; unfold lte ; simpl ; auto.
  Qed.
End PreOrd.

Section PartialOrd.
  Global Instance unit_PartialOrd : PartialOrd unit.
  Proof.
    constructor ; eauto with typeclass_instances.
    - unfold Antisymmetric ; intros ; destruct x,y ; unfold lte ; simpl ; auto.
    - unfold Proper,"==>",impl,Basics.impl ; intros ; destruct x,y,y0 ; simpl ; auto.
  Qed.
  Definition unit_pord_dec : unit -> unit -> option comparison := const2 $ Some Eq.
  Global Instance unit_PartialOrdDec : PartialOrdDec unit := { pord_dec := unit_pord_dec }.
  Global Instance unit_PartialOrd_RDC : PartialOrd_RDC unit.
  Proof.
    constructor ; intros ; destruct x,y ; simpl
    ; unfold pord_dec,unit_pord_dec,eqv in * ; simpl in *
    ; unfold unit_pord_dec in * ; simpl in * ; try congruence.
    - simpl. destruct H.
      exfalso ; apply H0 ; auto.
    - destruct H.
      exfalso ; apply H0 ; auto.
    - destruct H.
      exfalso ; apply H ; constructor.
  Qed.
End PartialOrd.

Section TotalOrd.
  Global Instance unit_TotalOrd : TotalOrd unit.
  Proof.
    constructor ; eauto with typeclass_instances ; intros.
    unfold "~" at 1 ; intros.
    destruct H.
    apply H.
    destruct x,y ; unfold lte ; simpl ; auto.
  Qed.
  Definition unit_tord_dec (x:unit) (y:unit) : comparison := Eq.
  Global Instance unit_TotalOrdDec : TotalOrdDec unit := { tord_dec := unit_tord_dec }.
  Global Instance unit_TotalOrd_RDC : TotalOrd_RDC unit.
  Proof.
    constructor ; intros ; destruct x,y ; simpl
    ; unfold tord_dec,unit_tord_dec,eqv in * ; simpl in *
    ; unfold unit_tord_dec in * ; simpl in * ; try congruence.
    - destruct H.
      exfalso ; apply H0 ; auto.
    - destruct H.
      exfalso ; apply H0 ; auto.
  Qed.
End TotalOrd.

Section Lattice.
  Definition unit_meet : unit -> unit -> unit := const2 tt.
  Definition unit_join : unit -> unit -> unit := const2 tt.

  Global Instance unit_lattice : Lattice unit :=
    { lmeet := unit_meet
    ; ljoin := unit_join
    }.

  Global Instance unit_LatticeWF : LatticeWF unit.
  Proof. constructor ; eauto with typeclass_instances ; intros ; constructor ;
      destruct t1, t2 ; compute ; auto.
  Qed.
End Lattice.

Section BoundedLattice.
  Global Instance unit_BoundedLattice : BoundedLattice unit :=
    { ltop := tt
    ; lbot := tt
    }.
  Global Instance unit_BoundedLatticeWF : BoundedLatticeWF unit.
  Proof. constructor ; intros ; destruct t ; simpl in * ; reflexivity.
  Qed.
End BoundedLattice.
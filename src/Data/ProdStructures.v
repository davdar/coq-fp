Require Export Data.Prod.

Require Import Data.Ascii.
Require Import Data.Bool.
Require Import Relations.RelDec.
Require Import Structures.EqDec.
Require Import Structures.Eqv.
Require Import Structures.Lte.
Require Import Structures.Monoid.
Require Import Structures.RelationClasses.
Require Import Structures.Show.

Import EqDecNotation.
Import LteNotation.
Import EqvNotation.
Import MonoidNotation.

Section EqDec.
  Context {A B} {AED:EqDec A} {BED:EqDec B}.

  Definition prod_eq_dec (ab1:A*B) (ab2:A*B) : bool :=
    let '((a1,b1),(a2,b2)) := (ab1,ab2) in a1 =! a2 && b1 =! b2.
  Global Instance prod_EqDec : EqDec (A*B) := { eq_dec := prod_eq_dec }.

  Context {ARDC:RelDecCorrect (T:=A) eq_dec eq}.
  Context {BRDC:RelDecCorrect (T:=B) eq_dec eq}.

  Global Instance prod_Eq_RelDecCorrect : RelDecCorrect (T:=A*B) eq_dec eq.
  Proof. constructor ; intros x y ;
      destruct x ; destruct y ; simpl in * ; unfold prod_eq_dec ;
      constructor ; intros.
    apply andb_true_iff in H ; destruct H.
      assert (a=a0) ; [ apply rel_dec_correct | subst ] ; auto.
      assert (b=b0) ; [ apply rel_dec_correct | subst ] ; auto.
    inversion H ; subst ; clear H.
    apply andb_true_iff ; constructor ; apply rel_dec_correct ; reflexivity.
  Qed.
End EqDec.

Section Eqv.
  Context {A B} {AE:Eqv A} {BE:Eqv B}.

  Inductive prod_eqv : A*B -> A*B -> Prop :=
    ProdEqv : forall a1 b1 a2 b2,
      a1 ~= a2 -> b1 ~= b2 -> prod_eqv (a1,b1) (a2,b2).

  Global Instance prod_Eqv : Eqv (A*B) := { eqv := prod_eqv }.

  Context {AEE:Equivalence (A:=A) eqv} {BEE:Equivalence (A:=B) eqv}.

  Global Instance prod_Equivalence : Equivalence (A:=A*B) eqv.
  Proof. constructor.
    unfold Reflexive ; intros.
      destruct x. constructor ; reflexivity.
    unfold Symmetric ; intros.
      destruct x ; destruct y ; inversion H ; subst ; clear H ; constructor ;
          symmetry ; auto.
    unfold Transitive ; intros.
      destruct x ; destruct y ; inversion H ; inversion H0 ; subst ; clear H H0 ;
          constructor.
        transitivity a0 ; auto. 
        transitivity b0 ; auto. 
  Qed.
End Eqv.

Section EqvDec.
  Context {A B} {AED:EqvDec A} {BED:EqvDec B}.

  Definition prod_eqv_dec (ab1:A*B) (ab2:A*B) : bool :=
    let '((a1,b1),(a2,b2)) := (ab1,ab2) in a1 ~=! a2 && b1 ~=! b2.

  Global Instance prod_EqvDec : EqvDec (A*B) := { eqv_dec := prod_eqv_dec }.

  Context {AE:Eqv A} {ARDC:RelDecCorrect (T:=A) eqv_dec eqv}.
  Context {BE:Eqv B} {BRDC:RelDecCorrect (T:=B) eqv_dec eqv}.

  Global Instance prod_Eqv_RelDecCorrect : RelDecCorrect (T:=A*B) eqv_dec eqv.
  Proof. constructor ; destruct x ; destruct y ; constructor ; intros ;
      simpl in * ; unfold prod_eqv_dec in *.
    apply andb_true_iff in H ; destruct H.
      constructor ; apply rel_dec_correct ; auto.
    inversion H ; subst ; clear H.
      apply andb_true_iff ; constructor ; apply rel_dec_correct ; auto.
  Qed.
End EqvDec.

Section Lte.
  Context {A B} {AL:Lte A} {BL:Lte B}.

  Inductive prod_lte : A*B -> A*B -> Prop :=
    | FstLte : forall a1 b1 a2 b2,
        a1 '< a2 -> prod_lte (a1,b1) (a2,b2)
    | SndLte : forall a1 b1 a2 b2,
        a1 '<=> a2 -> b1 '<= b2 -> prod_lte (a1,b1) (a2,b2).

  Global Instance prod_Lte : Lte (A*B) := { lte := prod_lte }.

  Context {ALPO:PreOrder (A:=A) lte} {BLPO:PreOrder (A:=B) lte}.

  Global Instance prod_PreOrder : PreOrder (A:=A*B) lte.
  Proof. constructor.
    unfold Reflexive ; intros.
      destruct x ; apply SndLte ; reflexivity.
    unfold Transitive ; intros.
      destruct x ; destruct y ; destruct z ;
          inversion H ; inversion H0 ; subst ; clear H H0.
        apply FstLte.
          transitivity a0 ; auto.
        apply FstLte.
          unfold lt in * ; unfold order_eqv in *.
          inversion H2 ; inversion H9 ; subst ; clear H2 H9.
          constructor.
            transitivity a0 ; auto.
            unfold not in * ; intros ; apply H0 ; transitivity a1 ; auto.
        apply FstLte.
          unfold lt in * ; unfold order_eqv in *.
          inversion H4 ; inversion H8 ; subst ; clear H4 ; clear H8.
          constructor.
            transitivity a0 ; auto.
            unfold not in * ; intros ; apply H2 ; transitivity a ; auto.
        apply SndLte.
          transitivity a0 ; auto.
          transitivity b0 ; auto.
  Qed.
End Lte.

Section LteDec.
  Context {A B} {ALD:LteDec A} {BLD:LteDec B}.

  Definition prod_lte_dec (ab1:A*B) (ab2:A*B) : bool :=
    let '((a1,b1),(a2,b2)) := (ab1,ab2) in
    if a1 '<! a2 then true
    else if a1 '>! a2 then false
    else b1 '<=! b2.

  Global Instance prod_LteDec : LteDec (A*B) := { lte_dec := prod_lte_dec }.

  Context {AL:Lte A} {ARDC:RelDecCorrect (T:=A) lte_dec lte}.
  Context {BL:Lte B} {BRDC:RelDecCorrect (T:=B) lte_dec lte}.

  Global Instance prod_Lte_RelDecCorrect : RelDecCorrect (T:=A*B) lte_dec lte.
  Admitted.
End LteDec.

Section Show.
  Context {A B} {AS:Show A} {BS:Show B}.

  Section prod_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition prod_show (ab:A*B) : R :=
      let (a,b) := ab in
         rawshow_char "("%char
      ** show a
      ** rawshow_string ", "
      ** show b
      ** rawshow_char ")"%char.
  End prod_show.

  Global Instance prod_Show : Show (A*B) := { show := prod_show }.
End Show.
Require Import Equivalence.

Require Import StdBool.
Require Import StdAscii.
Require Import StdString.
Import BoolNotation.
Require Import Eq.
Import EqNotation.
Require Import Eqv.
Import EqvNotation.
Require Import Lte.
Import LteNotation.
Require Import RelDec.
Require Import Show.
Require Import Monoid.
Import MonoidNotation.
Require Import Morphism.

Section EqDec.
  Context {A B} {AED:EqDec A} {BED:EqDec B}.

  Definition sum_eq_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 =! a2
    | inr b1, inr b2 => b1 =! b2
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
    | InlSumEqv : forall a1 a2 , a1 ~= a2 -> sum_eqv (inl a1) (inl a2)
    | InrSumEqv : forall b1 b2, b1 ~= b2 -> sum_eqv (inr b1) (inr b2).

  Global Instance sum_Eqv : Eqv (A+B) := { eqv := sum_eqv }.

  Context {AEE:Equivalence (A:=A) eqv} {BEE:Equivalence (A:=B) eqv}.

  Global Instance sum_Equivalence : Equivalence (A:=A+B) eqv.
  Admitted.
End Eqv.

Section EqvDec.
  Context {A B} {AED:EqvDec A} {BED:EqvDec B}.

  Definition sum_eqv_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 ~=! a2
    | inr b1, inr b2 => b1 ~=! b2
    | _, _ => false
    end.

  Global Instance sum_EqvDec : EqvDec (A+B) := { eqv_dec := sum_eqv_dec }.

  Context {AE:Eqv A} {ARDC:RelDecCorrect (T:=A) eqv_dec eqv}.
  Context {BE:Eqv B} {BRDC:RelDecCorrect (T:=B) eqv_dec eqv}.

  Global Instance sum_Eqv_RelDecCorrect : RelDecCorrect (T:=A+B) eqv_dec eqv.
  Admitted.
End EqvDec.

Section Lte.
  Context {A B} {AL:Lte A} {BL:Lte B}.

  Inductive sum_lte : A+B -> A+B -> Prop :=
    | InlSumLte : forall a1 a2, a1 '<= a2 -> sum_lte (inl a1) (inl a2)
    | InrSumLte : forall b1 b2, b1 '<= b2 -> sum_lte (inr b1) (inr b2).
      
  Global Instance sum_Lte : Lte (A+B) := { lte := sum_lte }.

  Context {ALPO:PreOrder (A:=A) lte} {BLPO:PreOrder (A:=B) lte}.

  Global Instance sum_PreOrder : PreOrder (A:=A+B) lte.
  Proof. constructor.
    unfold Reflexive ; intros.
      destruct x ; constructor ; reflexivity.
    unfold Transitive ; intros.
      destruct x ; destruct y ; destruct z ;
          inversion H ; inversion H0 ; subst ; clear H H0.
        constructor ; transitivity a0 ; auto.
        constructor ; transitivity b0 ; auto.
  Qed.
End Lte.

Section LteDec.
  Context {A B} {ALD:LteDec A} {BLD:LteDec B}.

  Definition sum_lte_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 '<=! a2
    | inr b1, inr b2 => b1 '<=! b2
    | _, _ => false
    end.

  Global Instance sum_LteDec : LteDec (A+B) := { lte_dec := sum_lte_dec }.

  Context {AL:Lte A} {ARDC:RelDecCorrect (T:=A) lte_dec lte}.
  Context {BL:Lte B} {BRDC:RelDecCorrect (T:=B) lte_dec lte}.

  Global Instance sum_Lte_RelDecCorrect : RelDecCorrect (T:=A+B) lte_dec lte.
  Admitted.
End LteDec.

Section Show.
  Context {A B} {AS:Show A} {BS:Show B}.

  Section sum_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition sum_show (ab:A+B) : R :=
      let (tag,payload) :=
        match ab with
        | inl a => ("inl"%string, show a)
        | inr b => ("inr"%string, show b)
        end
      in rawshow_char "("%char
      ** rawshow_string tag
      ** rawshow_char " "%char
      ** payload
      ** rawshow_char ")"%char.
  End sum_show.

  Global Instance sum_Show : Show (A+B) := { show := sum_show }.
End Show.

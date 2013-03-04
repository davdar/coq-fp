Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Ord.
Require Import FP.Structures.Multiplicative.
Require Import FP.Relations.RelDec.
Require Import FP.Relations.Setoid.
Require Import FP.Data.Bool.
Require Import FP.Data.Function.

Import MultiplicativeNotation.
Import EqDecNotation.
Import BoolNotation.
Import EqvNotation.
Import OrdNotation.
Import FunctionNotation.

Section EqDec.
  Context {A B} {AED:EqDec A} {BED:EqDec B}.

  Definition prod_eq_dec (ab1:A*B) (ab2:A*B) : bool :=
    let '((a1,b1),(a2,b2)) := (ab1,ab2) in a1 =! a2 && b1 =! b2.
  Global Instance prod_EqDec : EqDec (A*B) := { eq_dec := prod_eq_dec }.

  Context {ARDC:RelDecCorrect A eq eq_dec}.
  Context {BRDC:RelDecCorrect B eq eq_dec}.

  Global Instance prod_Eq_RelDecCorrect : RelDecCorrect (A*B) eq eq_dec.
  Admitted.
End EqDec.

Section Eqv.
  Context {A B} {AE:Eqv A} {BE:Eqv B}.

  Inductive prod_eqv : A*B -> A*B -> Prop :=
    ProdEqv : forall a1 b1 a2 b2,
      a1 ~= a2 -> b1 ~= b2 -> prod_eqv (a1,b1) (a2,b2).

  Global Instance prod_Eqv : Eqv (A*B) := { eqv := prod_eqv }.

  Context {AEE:EqvWF A} {BEE:EqvWF B}.

  Global Instance prod_Equivalence : EqvWF (A*B).
  Proof. repeat constructor.
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

  Context {AE:Eqv A} {ARDC:RelDecCorrect A eqv eqv_dec}.
  Context {BE:Eqv B} {BRDC:RelDecCorrect B eqv eqv_dec}.

  Global Instance prod_Eqv_RelDecCorrect : RelDecCorrect (A*B) eqv eqv_dec.
  Admitted.
End EqvDec.

Section Ord.
  Context {A} {AE:Eqv A} {AL:Ord A}.
  Context {B} {BL:Ord B}.

  Inductive prod_lt : A*B -> A*B -> Prop :=
    | SndLte : forall a1 b1 a2 b2,
        (a1 ~= a2) -> (b1 < b2) -> prod_lt (a1,b1) (a2,b2)
    | FstLte : forall a1 b1 a2 b2,
        (a1 < a2) -> prod_lt (a1,b1) (a2,b2).

  Global Instance prod_Ord : Ord (A*B) := { lt := prod_lt }.
End Ord.

Section OrdDec.
  Context {A B:Type}.

  Definition prod_ord_dec_b (a_ord_dec:A -> A -> comparison) (b_ord_dec:B -> B -> comparison)
      (ab1:A*B) (ab2:A*B) : comparison :=
    let '((a1,b1),(a2,b2)) := (ab1,ab2) in
    match a1 `a_ord_dec` a2 with
    | Lt => Lt
    | Gt => Gt
    | Eq => b1 `b_ord_dec` b2
    end.

  Context {ALD:OrdDec A} {BLD:OrdDec B}.

  Definition prod_ord_dec : A*B -> A*B -> comparison := prod_ord_dec_b ord_dec ord_dec.

  Global Instance prod_OrdDec : OrdDec (A*B) := { ord_dec := prod_ord_dec }.
End OrdDec.

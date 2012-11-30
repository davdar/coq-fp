Require Export FP.Data.ProdPre.

Require Import FP.Data.AsciiPre.
Require Import FP.Data.StringPre.
Require Import FP.Data.NPre.

Require Import FP.Data.Lens.
Require Import FP.Data.Store.
Require Import FP.Data.Bool.
Require Import FP.Data.Function.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.Applicative.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Functor.
Require Import FP.Data.PrettyI.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Ord.
Require Import FP.Structures.RelationClasses.
Require Import FP.Structures.Show.
Require Import FP.Structures.Traversable.
Require Import FP.Structures.HasLens.

Import LensNotation.
Import CharNotation.
Import EqDecNotation.
Import OrdNotation.
Import EqvNotation.
Import MonoidNotation.
Import FunctorNotation.
Import FunctionNotation.
Import BoolNotation.
Import StringNotation.

Local Infix "*" := prod.

Section EqDec.
  Context {A B} {AED:EqDec A} {BED:EqDec B}.

  Definition prod_eq_dec (ab1:A*B) (ab2:A*B) : bool :=
    let '((a1,b1),(a2,b2)) := (ab1,ab2) in a1 '=! a2 && b1 '=! b2.
  Global Instance prod_EqDec : EqDec (A*B) := { eq_dec := prod_eq_dec }.

  Context {ARDC:RelDecCorrect (T:=A) eq_dec eq}.
  Context {BRDC:RelDecCorrect (T:=B) eq_dec eq}.

  Global Instance prod_Eq_RelDecCorrect : RelDecCorrect (T:=A*B) eq_dec eq.
  Admitted.
  (*
  Proof. constructor ; intros x y ;
      destruct x ; destruct y ; simpl in * ; unfold prod_eq_dec ;
      constructor ; intros.
    apply andb_true_iff in H ; destruct H.
      assert (a=a0) ; [ apply rel_dec_correct | subst ] ; auto.
      assert (b=b0) ; [ apply rel_dec_correct | subst ] ; auto.
    inversion H ; subst ; clear H.
    apply andb_true_iff ; constructor ; apply rel_dec_correct ; reflexivity.
  Qed.
  *)
End EqDec.

Section Eqv.
  Context {A B} {AE:Eqv A} {BE:Eqv B}.

  Inductive prod_eqv : A*B -> A*B -> Prop :=
    ProdEqv : forall a1 b1 a2 b2,
      a1 '~= a2 -> b1 '~= b2 -> prod_eqv (a1,b1) (a2,b2).

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
    let '((a1,b1),(a2,b2)) := (ab1,ab2) in a1 '~=! a2 && b1 '~=! b2.

  Global Instance prod_EqvDec : EqvDec (A*B) := { eqv_dec := prod_eqv_dec }.

  Context {AE:Eqv A} {ARDC:RelDecCorrect (T:=A) eqv_dec eqv}.
  Context {BE:Eqv B} {BRDC:RelDecCorrect (T:=B) eqv_dec eqv}.

  Global Instance prod_Eqv_RelDecCorrect : RelDecCorrect (T:=A*B) eqv_dec eqv.
  Admitted.
  (*
  Proof. constructor ; destruct x ; destruct y ; constructor ; intros ;
      simpl in * ; unfold prod_eqv_dec in *.
    apply andb_true_iff in H ; destruct H.
      constructor ; apply rel_dec_correct ; auto.
    inversion H ; subst ; clear H.
      apply andb_true_iff ; constructor ; apply rel_dec_correct ; auto.
  Qed.
  *)
End EqvDec.

Section Ord.
  Context {A B} {AL:Ord A} {BL:Ord B}.

  Inductive prod_lt : A*B -> A*B -> Prop :=
    | FstLte : forall a1 b1 a2 b2,
        a1 '< a2 -> prod_lt (a1,b1) (a2,b2)
    | SndLte : forall a1 b1 a2 b2,
        a1 '~= a2 -> b1 '< b2 -> prod_lt (a1,b1) (a2,b2).

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

Section Show.
  Context {A B} {AS:Show A} {BS:Show B}.

  Section prod_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition prod_show (ab:A*B) : R :=
      let (a,b) := ab in
         raw_char "("%char
      ** show a
      ** raw_string ", "
      ** show b
      ** raw_char ")"%char.
  End prod_show.

  Global Instance prod_Show : Show (A*B) := { show := prod_show }.
End Show.

Section Pretty.
  Context {A B} {AP:Pretty A} {BP:Pretty B}.

  Definition prod_pretty (ab:A*B) : doc :=
    let (a,b) := ab in
      group_d begin
        text_d "( " `concat_d`
        nest_d 2 (pretty a) `concat_d`
        line_d `concat_d`
        text_d ", " `concat_d`
        nest_d 2 (pretty b) `concat_d`
        line_d `concat_d`
        text_d ")"
      end.
  Global Instance prod_Pretty : Pretty (A*B) :=
    { pretty := prod_pretty }.
End Pretty.

Inductive on_fst B A := OnFst { un_on_fst : A*B }.
Arguments OnFst {B A} _.
Arguments un_on_fst {B A} _.

Section Functor.
  Definition prod_fmap_snd {A B C}
    (f:B -> C) (p:A*B) : A*C := let (x,y) := p in (x, f y).
  Global Instance prod_fst_Functor {A} : Functor (prod A) :=
    { fmap := fun _ _ => prod_fmap_snd }.

  Definition prod_fmap_fst {A B C}
      (f:A -> C) (p:on_fst B A) : on_fst B C :=
    let (x,y) := un_on_fst p in OnFst (f x, y).
  Global Instance prod_snd_Functor {B} : Functor (on_fst B) :=
    { fmap := fun _ _ => prod_fmap_fst }.
End Functor.

Section Traversable.
  Definition prod_sequence_snd {A} {u} {uA:Applicative u} {B} (p:A*u B) : u (A*B) :=
    let (a,b) := p in pair a <$> b.
  Global Instance prod_fst_Traversable {A} : Traversable (prod A) :=
    { tsequence := @prod_sequence_snd _ }.

  Definition prod_sequence_fst {B} {u} {uA:Applicative u} {A} (p:on_fst B (u A))
      : u (on_fst B A) :=
    let (a,b) := un_on_fst p in
    (fun x => OnFst (x,b)) <$> a.
  Global Instance prod_snd_Traversable {B} : Traversable (on_fst B) :=
    { tsequence := @prod_sequence_fst _ }.

  Definition sequence_fst {A B} {u} {uA:Applicative u} : (u A*B) -> u (A*B) :=
    fmap un_on_fst <.> tsequence <.> OnFst.
End Traversable.

Section Type_Monoid.
  Definition prod_Type_Monoid : Monoid Type :=
    {| Monoid_Semigroup := {| gtimes := prod |}
     ; gunit := (unit:Type)
    |}.
End Type_Monoid.

Section Lens.
  Definition fst_lens {A B} : lens (A*B) A :=
    Lens $ fun p =>
      let '(a,b) := p in
      Store (fun a => (a,b)) a.

  Definition snd_lens {A B} : lens (A*B) B :=
    Lens $ fun p =>
      let '(a,b) := p in
      Store (fun b => (a,b)) b.

  Global Instance prod_HasLens_fst {A B S} {HL:HasLens A S} : HasLens (A*B) S :=
    { get_lens := fst_lens '.' get_lens S }.
  Global Instance prod_HasLens_snd {A B} : HasLens (A*B) B :=
    { get_lens := snd_lens }.
End Lens.
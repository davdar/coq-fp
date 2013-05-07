Require Import FP.Structures.Show.
Require Import FP.Data.PrettyI.
Require Import FP.Data.N.
Require Import FP.Data.Function.
Require Import FP.Data.Type.
Require Import FP.Data.Ascii.
Require Import FP.Data.String.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Applicative.
Require Import FP.Structures.Multiplicative.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Traversable.
Require Import FP.Structures.HasLens.
Require Import FP.Data.Lens.
Require Import FP.Data.Store.

Import MultiplicativeNotation.
Import MonoidNotation.
Import CharNotation.
Import FunctionNotation.
Import FunctorNotation.
Import StringNotation.
Import NNotation.

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
  Section A.
    Context {A:Type}.
    Definition prod_fmap_snd {B C}
      (f:B -> C) (p:A*B) : A*C := let (x,y) := p in (x, f y).
    Global Instance prod_fst_Functor : FMap (prod A) :=
      { fmap := @prod_fmap_snd }.
  End A.

  Section B.
    Context {B:Type}.
    Definition prod_fmap_fst {A C}
        (f:A -> C) (p:on_fst B A) : on_fst B C :=
      let (x,y) := un_on_fst p in OnFst (f x, y).
    Global Instance prod_snd_Functor : FMap (on_fst B) :=
      { fmap := @prod_fmap_fst }.
  End B.
End Functor.

Section Traversable.
  Definition prod_sequence_snd {A:Type} {u} {uA:Applicative u} {B}
      (p:A*u B) : u (A*B) :=
    let (a,b) := p in fapply_fmap (pair a) b.
  Global Instance prod_fst_Traversable {A} : Traversable (prod A) :=
    { tsequence := @prod_sequence_snd _ }.

  Definition prod_sequence_fst {B} {u} {uA:Applicative u} {A} (p:on_fst B (u A))
      : u (on_fst B A) :=
    let (a,b) := un_on_fst p in
    fapply_fmap (fun x => OnFst (x,b)) a.
  Global Instance prod_snd_Traversable {B} : Traversable (on_fst B) :=
    { tsequence := @prod_sequence_fst _ }.

  Definition sequence_fst {A B} {u} {uA:Applicative u} : (u A*B) -> u (A*B) :=
    fapply_fmap un_on_fst '.' tsequence '.' OnFst.
End Traversable.

Section Lens.
  Definition fst_lens {A B} : lens (A*B) A :=
    Lens $ fun p =>
      let '(a,b) := p in
      Store (fun a => (a,b)) a.

  Definition snd_lens {A B} : lens (A*B) B :=
    Lens $ fun p =>
      let '(a,b) := p in
      Store (fun b => (a,b)) b.

  Global Instance prod_HasLens_fst {A B} : HasLens (A*B) A :=
    { get_lens := fst_lens }.
  Global Instance prod_HasLens_snd {A B} : HasLens (A*B) B :=
    { get_lens := snd_lens }.
End Lens.
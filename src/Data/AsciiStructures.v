Require Import FP.Data.Ascii.
Require Import FP.Data.AsciiRelations.
Require Import FP.Data.Bool.
Require Import FP.Data.Function.
Require Import FP.Data.List.
Require Import FP.Data.ListStructures.
Require Import FP.Data.N.
Require Import FP.Data.NRelations.
Require Import FP.Structures.Convertible.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Ord.
Require Import FP.Structures.Show.

Import MonoidNotation.
Import BoolNotation.
Import FunctionNotation.
Import ListNotation.
Import OrdNotation.
Import CharNotation.
Import NNotation.

Section predicates.
  Definition is_alpha (c:ascii) : bool :=
    let n := convert_to N c in
    65 <=! n <=! 90 || 97 <=! n <=! 122.

  Definition is_numeric (c:ascii) : bool :=
    let n := convert_to N c in
    48 <=! n <=! 57.

  Definition is_whitespace : ascii -> bool :=
    foldl orf (const false) $ fmap eq_dec $
      [ space ; newline ; tab ; carriage_return ].
End predicates.

Section Show.
  Section ascii_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition ascii_show (c:ascii) : R :=
         raw_char "'"%char
      ** raw_char c
      ** raw_char "'"%char.
  End ascii_show.

  Global Instance ascii_Show : Show ascii := { show := ascii_show }.
End Show.
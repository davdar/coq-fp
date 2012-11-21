Require Export Data.AsciiPre.

Require Import Data.FunctionPre.

Require Import Data.Bool.
Require Import Data.List.
Require Import Data.N.
Require Import Data.Prod.
Require Import Structures.EqDec.
Require Import Structures.Eqv.
Require Import Structures.Functor.
Require Import Structures.Monoid.
Require Import Structures.Ord.
Require Import Structures.Show.
Require Import Structures.Convertible.

Import CharNotation.
Import EqvNotation.
Import FunctionNotation.
Import MonoidNotation.
Import OrdNotation.
Import BoolNotation.
Import ListNotation.
Import NNotation.

Section EqDec.
  Definition ascii_eq_dec := eq_dec `on` ascii2prod.

  Global Instance ascii_EqDec : EqDec ascii := { eq_dec := ascii_eq_dec }.
End EqDec.

Section Eqv.
  Global Instance ascii_Eqv : Eqv ascii := { eqv := eq }.
End Eqv.

Section EqvDec.
  Global Instance ascii_EqvDec : EqvDec ascii := { eqv_dec := eq_dec }.
End EqvDec.

Section Ord.
  Definition ascii_lt := lt `on` ascii2prod.

  Global Instance ascii_Ord : Ord ascii := { lt := ascii_lt }.
End Ord.

Section OrdDec.
  Definition ascii_ord_dec := ord_dec `on` ascii2prod.

  Global Instance ascii_OrdDec : OrdDec ascii := { ord_dec := ascii_ord_dec  }.
End OrdDec.

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

Definition space := " "%char.
Definition newline := "012"%char.
Definition tab := "013"%char.
Definition carriage_return := "015"%char.

Section predicates.
  Definition is_alpha (c:ascii) : bool:=
    let n := convert (to:=N) c in
    65%N '<=! n '<=! 90%N || 97%N '<=! n '<=! 122%N.

  Definition is_numeric (c:ascii) : bool :=
    let n := convert (to:=N) c in
    48%N '<=! n '<=! 57%N.

  Definition is_whitespace : ascii -> bool :=
    foldl orf (const false) $ fmap eqv_dec $
      [ space ; newline ; tab ; carriage_return ].
End predicates.

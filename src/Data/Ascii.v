Require Coq.Strings.Ascii.

Require Import FP.Data.N.
Require Import FP.Structures.Convertible.

Definition ascii := Ascii.ascii.
Definition Ascii := Ascii.Ascii.

Module CharNotation.
  Delimit Scope char_scope with char.
End CharNotation.
Import CharNotation.

Definition ascii2prod c :=
  let '(Ascii b1 b2 b3 b4 b5 b6 b7 b8) := c in (b1, b2, b3, b4, b5, b6, b7, b8).
Definition prod2ascii p :=
  let '(b1, b2, b3, b4, b5, b6, b7, b8) := p in (Ascii b1 b2 b3 b4 b5 b6 b7 b8).
Instance ascii_N_Convertible : Convertible ascii N :=
  { convert := Ascii.N_of_ascii }.
Instance N_ascii_Convertible : Convertible N ascii :=
  { convert := Ascii.ascii_of_N }.

Section constants.
  Definition space := " "%char.
  Definition newline := "010"%char.
  Definition tab := "011"%char.
  Definition carriage_return := "013"%char.
End constants.
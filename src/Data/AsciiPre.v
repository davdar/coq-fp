Require Coq.Strings.Ascii.

Require Import Data.NPre.
Require Import Structures.Convertible.

Definition ascii := Ascii.ascii.
Definition Ascii := Ascii.Ascii.

Module CharNotation.
  Delimit Scope char_scope with char.
End CharNotation.

Definition ascii2prod c :=
  let '(Ascii b1 b2 b3 b4 b5 b6 b7 b8) := c in (b1, b2, b3, b4, b5, b6, b7, b8).
Definition prod2ascii p :=
  let '(b1, b2, b3, b4, b5, b6, b7, b8) := p in (Ascii b1 b2 b3 b4 b5 b6 b7 b8).
Instance ascii_prod_Convertible : Convertible ascii (bool * bool * bool * bool * bool * bool * bool * bool) :=
  { convert := ascii2prod }.
Instance prod_ascii_Convertible : Convertible (bool * bool * bool * bool * bool * bool * bool * bool) ascii :=
  { convert := prod2ascii }.
  
Instance ascii_nat_Convertible : Convertible ascii nat :=
  { convert := Ascii.nat_of_ascii }.
Instance nat_ascii_Convertible : Convertible nat ascii :=
  { convert := Ascii.ascii_of_nat }.

Instance ascii_N_Convertible : Convertible ascii N :=
  { convert := Ascii.N_of_ascii }.
Instance N_ascii_Convertible : Convertible N ascii :=
  { convert := Ascii.ascii_of_N }.


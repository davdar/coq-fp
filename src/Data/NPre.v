Require BinNums.
Require BinNat.

Require Import Structures.Convertible.

Definition N := BinNums.N.
Definition N0 := BinNums.N0.
Definition Npos := BinNums.Npos.

Module NNotation.
  Delimit Scope N_scope with N.
End NNotation.
Open Scope N_scope.

Instance N_nat_Convertible : Convertible N nat :=
  { convert := BinNat.N.to_nat }.
Instance nat_N_Convertible : Convertible nat N :=
  { convert := BinNat.N.of_nat }.



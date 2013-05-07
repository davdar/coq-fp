Require BinNums.
Require BinInt.

Definition Z := BinNums.Z.

Definition Z0 := BinNums.Z0.
Definition Zpos := BinNums.Zpos.
Definition Zneg := BinNums.Zneg.

Module ZNotation.
  Delimit Scope Z_scope with Z.
End ZNotation.

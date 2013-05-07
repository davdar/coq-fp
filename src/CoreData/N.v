Require Coq.Numbers.BinNums.
Require Coq.NArith.BinNat.

Definition N := BinNums.N.
Definition N0 := BinNums.N0.
Definition Npos := BinNums.Npos.

Module NNotation.
  Delimit Scope N_scope with N.
  Open Scope N_scope.
End NNotation.
Import NNotation.

Definition N2Z (n:N) : BinNums.Z :=
  match n with
  | N0 => BinNums.Z0
  | Npos p => BinNums.Zpos p
  end.
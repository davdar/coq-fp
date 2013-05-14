Require Coq.Numbers.BinNums.

Definition positive := BinNums.positive.
Definition xH := BinNums.xH.
Definition xO := BinNums.xO.
Definition xI := BinNums.xI.

Module PositiveNotation.
  Delimit Scope positive_scope with positive.
End PositiveNotation.
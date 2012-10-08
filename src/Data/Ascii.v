Require Export Coq.Strings.Ascii.

Definition ascii2prod c :=
  let '(Ascii b1 b2 b3 b4 b5 b6 b7 b8) := c in (b1, b2, b3, b4, b5, b6, b7, b8).


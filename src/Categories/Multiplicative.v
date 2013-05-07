Require Import FP.Categories.Monoid.

Class Times T := { times_gtimes : GTimes T }.
Definition times {T} `{! Times T } : T -> T -> T := gtimes (GTimes:=times_gtimes).

Class One T := { one_gunit : GUnit T }.
Definition one {T} `{! One T } : T := gunit (GUnit:=one_gunit).

Class Div T := { div_gdiv : GDiv T }.
Definition div {T} `{! Div T } : T -> T -> T := gdiv (GDiv:=div_gdiv).

Class Inv T := { inv_ginv : GInv T }.
Definition inv {T} `{! Inv T } : T -> T := ginv (GInv:=inv_ginv).

Module MultiplicativeNotation.
  Infix "*" := times.
  Infix "/" := div.
End MultiplicativeNotation.
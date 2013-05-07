Require Import FP.Categories.Monoid.

Class Plus T := { plus_gtimes : GTimes T }.
Definition plus {T} `{! Plus T } : T -> T -> T := gtimes (GTimes:=plus_gtimes).

Class Zero T := { zero_gunit : GUnit T }.
Definition zero {T} `{! Zero T } : T := gunit (GUnit:=zero_gunit).

Class Minus T := { minus_gdiv : GDiv T }.
Definition minus {T} `{! Minus T } : T -> T -> T := gdiv (GDiv:=minus_gdiv).

Class Neg T := { neg_ginv : GInv T }.
Definition neg {T} `{! Neg T } : T -> T := ginv (GInv:=neg_ginv).

Module AdditiveNotation.
  Infix "+" := plus.
  Infix "-" := minus.
End AdditiveNotation.
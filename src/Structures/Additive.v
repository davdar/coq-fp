Require Import FP.Structures.Monoid.

Class Plus T :=
  { plus_gtimes :> GTimes T }.
Definition plus {T} {T_Plus : Plus T} : T -> T -> T := gtimes.

Class Zero T :=
  { zero_gtimes :> GUnit T }.
Definition zero {T} {T_Zero : Zero T} : T := gunit.

Class Minus T :=
  { minus_gdiv :> GDiv T }.
Definition minus {T} {T_Minus : Minus T} : T -> T -> T := gdiv.

Class Neg T :=
  { neg_ginv :> GInv T }.
Definition neg {T} {T_Neg : Neg T} : T -> T := ginv.

Module AdditiveNotation.
  Infix "+" := plus.
  Infix "-" := minus.
End AdditiveNotation.

Class Semiadditive T :=
  { semiadditive_semigroup :> Semigroup T }.
Class MinusSemiadditive T :=
  { minus_semiadditive_div_semigroup :> DivSemigroup T }.
Class Additive T :=
  { additive_monoid :> Monoid T }.
Class NegAdditive T :=
  { neg_additive_inv_monoid :> InvMonoid T }.

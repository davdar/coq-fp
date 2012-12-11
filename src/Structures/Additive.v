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
  { semiadditive_Semigroup :> Semigroup T }.
Instance Semiadditive_Plus {T} {S:Semiadditive T} : Plus T := {}.

Class MinusSemiadditive T :=
  { minus_semiadditive_DivSemigroup :> DivSemigroup T }.
Instance MinusSemiadditive_Plus {T} {S:MinusSemiadditive T} : Plus T := {}.
Instance MinusSemiadditive_Minus {T} {S:MinusSemiadditive T} : Minus T := {}.

Class Additive T :=
  { additive_Monoid :> Monoid T }.
Instance Additive_Plus {T} {S:Additive T} : Plus T := {}.
Instance Additive_Zero {T} {S:Additive T} : Zero T := {}.

Class MinusAdditive T :=
  { minus_additive_DivMonoid :> DivMonoid T }.
Instance MinusAdditive_Plus {T} {S:MinusAdditive T} : Plus T := {}.
Instance MinusAdditive_Zero {T} {S:MinusAdditive T} : Zero T := {}.
Instance MinusAdditive_Minus {T} {S:MinusAdditive T} : Minus T := {}.

Class NegAdditive T :=
  { neg_additive_InvMonoid :> InvMonoid T }.
Instance NegAdditive_Plus {T} {S:NegAdditive T} : Plus T := {}.
Instance NegAdditive_Zero {T} {S:NegAdditive T} : Zero T := {}.
Instance NegAdditive_Neg {T} {S:NegAdditive T} : Neg T := {}.
Instance NegAdditive_Minus {T} {S:NegAdditive T} : Minus T := {}.

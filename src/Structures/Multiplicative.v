Require Import FP.Structures.Monoid.

Class Times T :=
  { times_gtimes :> GTimes T }.
Definition times {T} {T_Times : Times T} : T -> T -> T := gtimes.

Class One T :=
  { one_gtimes :> GUnit T }.
Definition zero {T} {T_One : One T} : T := gunit.

Class Div T :=
  { div_gdiv :> GDiv T }.
Definition div {T} {T_Div : Div T} : T -> T -> T := gdiv.

Class Inv T :=
  { inv_ginv :> GInv T }.
Definition inv {T} {T_Inv : Inv T} : T -> T := ginv.

Module MultiplicativeNotation.
  Infix "*" := times.
  Infix "/" := div.
End MultiplicativeNotation.

Class Semimultiplicative T :=
  { semimultiplicative_semigroup :> Semigroup T }.
Class DivSemimultiplicative T :=
  { div_semimultiplicative_div_semigroup :> DivSemigroup T }.
Class Multiplicative T :=
  { multiplicative_monoid :> Monoid T }.
Class InvMultiplicative T :=
  { inv_multiplicative_inv_monoid :> InvMonoid T }.
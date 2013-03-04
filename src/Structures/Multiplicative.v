Require Import FP.Structures.Monoid.

Class Times T :=
  { times_gtimes :> GTimes T }.
Definition times {T} {Times:Times T} : T -> T -> T := gtimes.

Class One T :=
  { one_gtimes :> GUnit T }.
Definition one {T} {One:One T} : T := gunit.

Class Div T :=
  { div_gdiv :> GDiv T }.
Definition div {T} {Div:Div T} : T -> T -> T := gdiv.

Class Inv T :=
  { inv_ginv :> GInv T }.
Definition inv {T} {Inv:Inv T} : T -> T := ginv.

Module MultiplicativeNotation.
  Infix "*" := times.
  Infix "/" := div.
End MultiplicativeNotation.

Class Semimultiplicative T :=
  { semimultiplicative_Semigroup :> Semigroup T }.
Instance Semimultiplicative_Times {T} {S:Semimultiplicative T} : Times T := {}.

Class DivSemimultiplicative T :=
  { div_semimultiplicative_DivSemigroup :> DivSemigroup T }.
Instance DivSemimultiplicative_Times {T} {S:DivSemimultiplicative T} : Times T := {}.
Instance DivSemimultiplicative_Div {T} {S:DivSemimultiplicative T} : Div T := {}.

Class Multiplicative T :=
  { multiplicative_Monoid :> Monoid T }.
Instance Multiplicative_Times {T} {S:Multiplicative T} : Times T := {}.
Instance Multiplicative_One {T} {S:Multiplicative T} : One T := {}.

Class DivMultiplicative T :=
  { div_multiplicative_DivMonoid :> DivMonoid T }.
Instance DivMultiplicative_Times {T} {S:DivMultiplicative T} : Times T := {}.
Instance DivMultiplicative_One {T} {S:DivMultiplicative T} : One T := {}.
Instance DivMultiplicative_Div {T} {S:DivMultiplicative T} : Div T := {}.

Class InvMultiplicative T :=
  { inv_multiplicative_InvMonoid :> InvMonoid T }.
Instance InvMultiplicative_Times {T} {S:InvMultiplicative T} : Times T := {}.
Instance InvMultiplicative_One {T} {S:InvMultiplicative T} : One T := {}.
Instance InvMultiplicative_Inv {T} {S:InvMultiplicative T} : Div T := {}.
Instance InvMultiplicative_Div {T} {S:InvMultiplicative T} : Div T := {}.
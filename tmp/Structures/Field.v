Require Import FP.Structures.Additive.
Require Import FP.Structures.Multiplicative.

Class Field T :=
  { field_addition :> MinusAdditive T
  ; field_multiplication :> DivMultiplicative T
  }.
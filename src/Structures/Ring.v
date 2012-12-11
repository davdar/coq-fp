Require Import FP.Structures.Additive.
Require Import FP.Structures.Multiplicative.

Class Ring T :=
  { ring_addition : MinusAdditive T
  ; ring_multiplication : Multiplicative T
  }.


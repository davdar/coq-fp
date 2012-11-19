Require Import Monoid.

Class Field t :=
  { field_addition :> InverseMonoid t
  ; field_multiplication :> InverseMonoid t
  }.
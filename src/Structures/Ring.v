Require Import Monoid.

Class Ring t :=
  { ring_addition : InverseMonoid t
  ; ring_multiplication : Monoid t
  }.


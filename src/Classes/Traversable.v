Require Import FP.Classes.Applicative.

Class Traversable t :=
  { tsequence : forall {u} `{! Applicative u } {A}, t (u A) -> u (t A) }.
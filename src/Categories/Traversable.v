Require Import FP.Categories.Pointed.
Require Import FP.Categories.Applicative.

Class Traversable t :=
  { tsequence : forall {u} `{! FUnit u ,! FApply u } {A}, t (u A) -> u (t A) }.
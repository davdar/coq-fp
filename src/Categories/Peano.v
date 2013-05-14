Require Import FP.Categories.Copointed.
Require Import FP.Categories.Comonad.

Class Peano T :=
  { pzero : T
  ; psucc : T -> T
  ; coloopr : forall {w} `{! Counit w ,! Cobind w } {A}, (w A -> A) -> w A -> T -> A
  ; coloopl : forall {w} `{! Counit w ,! Cobind w } {A}, (w A -> A) -> w A -> T -> A
  }.

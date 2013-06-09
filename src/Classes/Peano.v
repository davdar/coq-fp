Require Import FP.Classes.Comonad.

Class Peano T :=
  { pzero : T
  ; psucc : T -> T
  ; coloopr : forall {w} `{! Comonad w } {A}, (w A -> A) -> w A -> T -> A
  ; coloopl : forall {w} `{! Comonad w } {A}, (w A -> A) -> w A -> T -> A
  }.

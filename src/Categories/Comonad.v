Require Import FP.Categories.Copointed.

Class Cobind (w:Type->Type) :=
  { cobind : forall {A B}, w A -> (w A -> B) -> w B }.

Section Comonad.
  Context {w} `{! Counit w ,! Cobind w }.
  Definition coret {A} : w A -> A := counit.
End Comonad.

Module ComonadNotation.
  Notation "'codo' x -< c1 => c2" := (cobind c1 (fun x => c2))
    (at level 100).
  Notation "'codo' x => c" := (codo x -< x => c)
    (at level 100).
End ComonadNotation.
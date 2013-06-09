Class Comonad (w:Type->Type) :=
  { coret : forall {A}, w A -> A
  ; cobind : forall {A B}, w A -> (w A -> B) -> w B
  }.

Module ComonadNotation.
  Notation "'codo' x -< c1 => c2" := (cobind c1 (fun x => c2))
    (at level 100).
  Notation "'codo' x => c" := (codo x -< x => c)
    (at level 100).
End ComonadNotation.
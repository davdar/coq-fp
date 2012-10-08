Definition flip {A B C} (f:A -> B -> C) (x:B) (y:A) : C := f y x.
Definition compose {A B C} (g:B -> C) (f:A -> B) (x:A) : C := g (f x).
Definition compose2 {A B C D} : (C -> D) -> (A -> B -> C) -> A -> B -> D :=
  compose compose compose.
Definition compose3 {A B C D E}
  : (D -> E) -> (A -> B -> C -> D) -> A -> B -> C -> E :=
    compose compose2 compose.

Definition on {A B C} (f:B -> B -> C) (m:A -> B)  (x:A) (y:A) := f (m x) (m y).

Module FunctionNotation.
  Notation "f $ x" := (f x)
    (at level 99, right associativity, only parsing).

  Notation "'begin' e1 'end'" := ((e1))
    (at level 0, only parsing).

  Infix "<.>" := compose (at level 45, right associativity).
  Infix "<..>" := compose2 (at level 45, right associativity).
  Infix "<...>" := compose2 (at level 45, right associativity).

  Notation "x ` f ` y" := (f x y)
    (at level 199, f at next level, right associativity, only parsing).
End FunctionNotation.
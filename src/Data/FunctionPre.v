Arguments id {A} _.

Definition Fun A B := A -> B.

Definition apply {A B} (f:A -> B) (x:A) : B := f x.
Definition apply_to {A B} (x:A) (f:A -> B) := f x.

Definition const {A B} (a:A) (_:B) := a.
Definition const2 {A B C} (a:A) (_:B) (_:C) := a.
Definition flip {A B C} (f:A -> B -> C) (b:B) (a:A) : C := f a b.
Definition compose {A B C} (g:B -> C) (f:A -> B) (a:A) : C := g (f a).
Definition compose2
    {A B C D} : (C -> D) -> (A -> B -> C) -> A -> B -> D :=
  compose compose compose.
Definition compose3
    {A B C D E} : (D -> E) -> (A -> B -> C -> D) -> A -> B -> C -> E :=
  compose compose2 compose.

Definition on {A B C} (f:B -> B -> C) (i:A -> B)  (x:A) (y:A) := f (i x) (i y).

Definition uncurry {A B C} (f:A -> B -> C) (p:A*B) : C :=
  let (a,b) := p in f a b.
Definition uncurry2 {A B C D} (f:A -> B -> C -> D) (p:A*B*C) : D :=
  let '(a,b,c) := p in f a b c.

Module FunctionNotation.
  Notation "f $ x" := (f x)
    (at level 99, right associativity, only parsing).

  Notation "'begin' e1 'end'" := ((e1))
    (at level 0, only parsing).

  Infix "<.>" := compose (at level 45, right associativity).
  Infix "<..>" := compose2 (at level 45, right associativity).
  Infix "<...>" := compose3 (at level 45, right associativity).

  Notation "x ` f ` y" := (f x y)
    (at level 98, f at next level, right associativity, only parsing).
End FunctionNotation.
Definition id {A} (a:A) : A := a.
Definition flip {A B C} (f:A -> B -> C) (b:B) (a:A) : C := f a b.

Definition apply {A B} (f:A -> B) (x:A) : B := f x.
Definition apply_to {A B} : A -> (A -> B) -> B := flip apply.

Definition compose {A B C} (g:B -> C) (f:A -> B) (a:A) : C := g (f a).
Definition compose2 {A B C D}
    : (C -> D) -> (A -> B -> C) -> A -> B -> D :=
  compose compose compose.
Definition compose3 {A B C D E}
    : (D -> E) -> (A -> B -> C -> D) -> A -> B -> C -> E :=
  compose compose2 compose.

Definition const {A B} (a:A) (_:B) : A := a.
Definition const2 {A B C} : A -> B -> C -> A := compose const const.

Definition on {A B C} (f:B -> B -> C) (i:A -> B)  (x:A) (y:A) := f (i x) (i y).

Definition uncurry {A B C} (f:A -> B -> C) (p:A*B) : C :=
  let (a,b) := p in f a b.
Definition uncurry2 {A B C D} : (A -> B -> C -> D) -> A*B*C -> D :=
  compose uncurry uncurry.
Definition curry {A B C} (f:A*B -> C) (a:A) (b:B) : C :=
  f (a,b).
Definition curry2 {A B C D} : (A*B*C -> D) -> A -> B -> C -> D :=
  compose curry curry.

Module FunctionNotation.
  Notation "f $ x" := (f x)
    (at level 99, right associativity, only parsing).

  Notation "'begin' e1 'end'" := ((e1))
    (at level 0, only parsing).

  Infix "'.'" := compose (at level 45, right associativity).
  Infix "'..'" := compose2 (at level 45, right associativity).
  Infix "'...'" := compose3 (at level 45, right associativity).

  Notation "x ` f ` y" := (f x y)
    (at level 98, f at next level, right associativity, only parsing).
End FunctionNotation.
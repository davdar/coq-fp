Definition Fun (A B:Type) := A -> B.

Definition id {A} (a:A) : A := a.
Arguments id {A} a /.
Definition flip {A B C} (f:A -> B -> C) (b:B) (a:A) : C := f a b.
Arguments flip {A B C} f b a /.

Definition apply {A B} (f:A -> B) (x:A) : B := f x.
Arguments apply {A B} f x /.
Definition apply_to {A B} : A -> (A -> B) -> B := flip apply.
Arguments apply_to {A B} x f /.

Definition compose {A B C} (g:B -> C) (f:A -> B) (a:A) : C := g (f a).
Arguments compose {A B C} g f a /.
Definition compose2 {A B C D}
    : (C -> D) -> (A -> B -> C) -> A -> B -> D :=
  compose compose compose.
Arguments compose2 {A B C D} _ _ _ _ /.
Definition compose3 {A B C D E}
    : (D -> E) -> (A -> B -> C -> D) -> A -> B -> C -> E :=
  compose compose2 compose.
Arguments compose3 {A B C D E} _ _ _ _ _ /.

Definition const {A B} (a:A) (_:B) : A := a.
Arguments const {A B} a _ /.
Definition const2 {A B C} : A -> B -> C -> A := compose const const.

Definition on {A B C} (f:B -> B -> C) (i:A -> B)  (x:A) (y:A) := f (i x) (i y).
Arguments on {A B C} f i x y /.

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
    (at level 89, right associativity, only parsing).

  Notation "'begin' e1 'end'" := ((e1))
    (at level 0, only parsing).

  Infix "'.'" := compose (at level 45, right associativity).
  Infix "'..'" := compose2 (at level 45, right associativity).
  Infix "'...'" := compose3 (at level 45, right associativity).

  Notation "x ` f ` y" := (f x y)
    (at level 88, f at next level, right associativity, only parsing).
End FunctionNotation.

Require Coq.Program.Basics.

Definition impl : Prop -> Prop -> Prop := Basics.impl.
Arguments impl _ _ /.
Arguments Basics.impl / _ _.
Definition follows : Prop -> Prop -> Prop := Basics.flip impl.
Arguments follows _ _ /.
Arguments Basics.flip {A B C} _ / _ _.
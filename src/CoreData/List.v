Require Coq.Lists.List.

Definition head := List.head.
Definition tail := List.tail.
Definition map := List.map.

Arguments cons {A} _ _.
Arguments app {A} _ _ .
Arguments length {A} _.
Arguments head {A} _.
Arguments tail {A} _.
Arguments map {A B} _ _.

Module ListNotation.
  Infix "++" := app.
  Infix "::" := cons.
  Notation "[ ]" := nil.
  Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).
End ListNotation.
Import ListNotation.

Fixpoint foldl {A R} (f:R -> A -> R) (i:R) (xs:list A) :=
  match xs with
  | nil => i
  | x::xs' => foldl f (f i x) xs'
  end.

Fixpoint foldr {A R} (f:A -> R -> R) (i:R) (xs:list A) :=
  match xs with
  | nil => i
  | x::xs' => f x (foldr f i xs')
  end.

Definition for_each {A B} : list A -> (A -> B) -> list B := fun x y => map y x.

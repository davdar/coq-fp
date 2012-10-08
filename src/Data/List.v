Require Export Coq.Lists.List.

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
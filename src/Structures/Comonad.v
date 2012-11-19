Require Import Data.Function.

Import FunctionNotation.

Class Comonad m :=
  { coret : forall {A}, m A -> A
  ; cobind : forall {A B}, m A -> (m A -> B) -> m B
  }.

Definition revcobind {m} {M:Comonad m} {A B} : (m A -> B) -> m A -> m B := flip cobind.
Definition cokleisli_compose {m} {M:Comonad m} {A B C} (g:m B -> C) (f:m A -> B) (aM:m A) : m C :=
  (aM `cobind` f) `cobind` g.
Definition cokleisli_revcompose {m} {M:Comonad m} {A B C} : (m A -> B) -> (m B -> C) -> m A -> m C :=
  flip cokleisli_compose.

Module ComonadNotation.
  Notation "'codo' x -< c1 => c2" := (cobind c1 (fun x => c2))
    (at level 100).
  Notation "'codo' x => c" := (codo x -< x => c)
    (at level 100).
    
  Infix "<<=" := revcobind (at level 51, right associativity).
  Infix "=>>" := cobind (at level 50, left associativity).
  Infix "=<=" := cokleisli_compose (at level 53, right associativity).
  Infix "=>=" := cokleisli_revcompose (at level 53, right associativity).
End ComonadNotation.
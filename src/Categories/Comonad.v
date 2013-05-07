Require Import FP.Categories.Copointed.

Class Cobind (w:Type->Type) :=
  { cobind : forall {A B}, w A -> (w A -> B) -> w B }.

Class Comonad (w:Type->Type) :=
  { Comonad_Counit : Counit w
  ; Comonad_Cobind : Cobind w
  }.
Hint Resolve Build_Comonad : typeclass_instances.
Hint Immediate Comonad_Counit : typeclass_instances.
Hint Immediate Comonad_Cobind : typeclass_instances.

Section Comonad.
  Context {w} `{! Comonad w }.
  Definition coret {A} : w A -> A := counit.
End Comonad.

Module ComonadNotation.
  Notation "'codo' x -< c1 => c2" := (cobind c1 (fun x => c2))
    (at level 100).
  Notation "'codo' x => c" := (codo x -< x => c)
    (at level 100).
    
  (*
  Infix "<<=" := revcobind (at level 51, right associativity).
  Infix "=>>" := cobind (at level 50, left associativity).
  Infix "=<=" := cokleisli_compose (at level 53, right associativity).
  Infix "=>=" := cokleisli_revcompose (at level 53, right associativity).
*)
End ComonadNotation.
(*

Definition revcobind {m} {M:Comonad m} {A B} : (m A -> B) -> m A -> m B := flip cobind.
Definition cokleisli_compose {m} {M:Comonad m} {A B C} (g:m B -> C) (f:m A -> B) (aM:m A) : m C :=
  (aM `cobind` f) `cobind` g.
Definition cokleisli_revcompose {m} {M:Comonad m} {A B C} : (m A -> B) -> (m B -> C) -> m A -> m C :=
  flip cokleisli_compose.

*)
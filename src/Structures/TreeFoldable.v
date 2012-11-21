Require Import FP.Structures.Comonad.

Class TreeFoldable A T :=
  { co_treefold : forall {m} {M:Comonad m} {B}, (A -> list (m B) -> B) -> m B -> T -> B }.

Class TreeBuildable A T :=
  { treebuild : (forall B, (A -> list B -> B) -> B -> B) -> T }.



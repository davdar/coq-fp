Require Import Structures.Monad.

Class MonadTrans t :=
  { lift : forall {m} {M:Monad m} {A}, m A -> t m A }.

Require Import Structures.Monad.

Class MonadT t :=
{ lift : forall {m} {M:Monad m} {A}, m A -> t m A }.

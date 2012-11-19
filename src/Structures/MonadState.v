Require Import Data.Function.
Require Import Structures.Monad.

Import FunctionNotation.
Import MonadNotation.

Class MonadState S m :=
  { get : m S
  ; put : S -> m unit
  }.

Definition modify {m S} {M:Monad m} {MS:MonadState S m} (f:S -> S) : m unit :=
  x <- get ;;
  put $ f x.

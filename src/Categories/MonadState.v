Require Import FP.Categories.Pointed.
Require Import FP.Categories.Monad.
Require Import FP.CoreData.

Import MonadNotation.
Import CoreDataNotation.

Class MonadState S m :=
  { get : m S
  ; put : S -> m unit
  }.

Section MonadState.
  Context {S m} `{! FUnit m ,! MBind m ,! MonadState S m }.

  Definition modify (f:S -> S) : m unit :=
    s <- get ;;
    put $ f s.
End MonadState.
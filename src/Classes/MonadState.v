Require Import FP.Classes.Monad.
Require Import FP.CoreData.

Import MonadNotation.
Import CoreDataNotation.

Class MonadState S m :=
  { mget : m S
  ; mput : S -> m unit
  }.
Arguments mget {S m MonadState} : simpl never.
Arguments mput {S m MonadState} _ : simpl never.

Section MonadState.
  Context {S m} `{! Monad m ,! MonadState S m }.

  Definition mmodify (f:S -> S) : m unit :=
    s <- mget ;;
    mput $ f s.
End MonadState.
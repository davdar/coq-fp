Require Export Data.Option.

Require Import Structures.Monad.
Require Import Structures.MonadPlus.

Instance option_Monad : Monad option.
Admitted.

Instance option_MonadPlus : MonadPlus option.
Admitted.

Section Monad.
  Context {m} {M:Monad m}.

  Global Instance option_t_Monad : Monad (option_t m).
  Admitted.

  Section MonadPlus.
    Global Instance option_t_MonadPlus : MonadPlus (option_t m).
    Admitted.
  End MonadPlus.
End Monad.


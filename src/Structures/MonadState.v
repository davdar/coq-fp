Require Import FP.Data.Function.
Require Import FP.Structures.Monad.
Require Import FP.Structures.Injection.

Import FunctionNotation.
Import MonadNotation.

Class MonadState S m :=
  { get : m S
  ; put : S -> m unit
  }.

Definition modify {m S} {M:Monad m} {MS:MonadState S m} (f:S -> S) : m unit :=
  x <- get ;;
  put $ f x.

Section iso_MonadState.
  Variable (n:Type -> Type).
  Context {m} {B:HasFunctorBijection m n} {S} {nMR:MonadState S n}.

  Definition iso_MonadState_get : m S := ffrom get.
  Definition iso_MonadState_put (s:S) : m unit := ffrom $ put s.
  Definition iso_MonadState : MonadState S m :=
    {| get := @iso_MonadState_get
     ; put := @iso_MonadState_put
    |}.
End iso_MonadState.
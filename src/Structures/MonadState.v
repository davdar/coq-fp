Require Import FP.Structures.Monad.
Require Import FP.Structures.EqvEnv.
Require Import FP.Structures.FUnit.
Require Import FP.Structures.Proxy.
Require Import FP.Data.Function.
Require Import FP.Relations.Setoid.

Import MonadNotation.
Import FunctionNotation.

Class MState (S:Type) (m:Type->Type) : Type :=
  { get : m S
  ; put : S -> m unit
  }.

Section MonadState.
  Context {m} {Monad_:Monad m} {S} {MState_:MState S m}.
  Definition modify (f:S -> S) : m unit :=
    x <- get ;;
    put $ f x.
End MonadState.

Section MonadStateWF.
  Context {S:Type} {m:Type->Type}.
  Context {Monad_:Monad m} {MState_:MState S m}.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {PE_R_E:Px (env_PER S)}.
  Context {PE_R_E':Px (env_PER_WF S)}.
  Context {PE_R_Eu:Px (env_PER unit)}.
  Context {PE_R_Eu':Px (env_PER_WF unit)}.
  Context {PE_R_t:forall {A} {aER:Px (env_PER A)}, Px (env_PER (m A))}.
  Context {PE_R_t' :
    forall {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)},
    Px (env_PER_WF (m A))}.


  Class MonadStateWF :=
    { mget_after_mput :
        forall
          (s:S) (sP:Proper env_eqv s),
            env_eqv
            (seq (put s) get)
            (seq (put s) (ret s))
    ; mput_after_mput :
        forall
          (s1:S) (s1P:Proper env_eqv s1)
          (s2:S) (s2P:Proper env_eqv s2),
            env_eqv
            (seq (put s1) (put s2))
            (put s2)
    }.
End MonadStateWF.
(*
Require Import FP.Data.Function.
Require Import FP.Structures.Monad.
Require Import FP.Structures.Injection.

Import FunctionNotation.
Import MonadNotation.

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
*)
Require Import FP.Structures.Monad.
Require Import FP.Structures.EqvRel.
Require Import FP.Structures.FUnit.
Require Import FP.Data.Function.

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
  Context {EqvEnvWF_:EqvEnvWF}.
  Context {E_R_S:E_R S}.
  Context {E_R_unit:E_R unit}.
  Context {E_R_m:forall {A} {aER:E_R A}, E_R (m A)}.

  Class MonadStateWF :=
    { mget_after_mput :
        forall
          (s:S) (s':S) (sP:E_eqv s s'),
            E_eqv
            (seq (put s) get)
            (seq (put s') (ret s'))
    ; mput_after_mput :
        forall
          (s1:S) (s1':S) (s1P:E_eqv s1 s1')
          (s2:S) (s2':S) (s2P:E_eqv s2 s2'),
            E_eqv
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
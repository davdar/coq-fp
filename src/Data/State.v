Require Import Data.Function.
Require Import Data.Prod.
Require Import Data.Type.
Require Import Structures.Functor.
Require Import Structures.Monad.
Require Import Structures.Multiplicative.
Require Import Structures.MonadState.
Require Import Data.Identity.

Import FunctionNotation.
Import FunctorNotation.
Import MonadNotation.
Import MultiplicativeNotation.

Inductive state_t S m A := StateT { un_state_t : S -> m (A * S) }.
Arguments StateT {S m A} _.
Arguments un_state_t {S m A} _ _.

Definition run_state_t {S m A} : S -> state_t S m A -> m (A * S) := flip un_state_t.
Definition eval_state_t {S m A} {M:Monad m} : S -> state_t S m A -> m A := fmap fst <..> run_state_t.
Definition exec_state_t {S m A} {M:Monad m} : S -> state_t S m A -> m S := fmap snd <..> run_state_t.

Section state_t.
  Context {m} {M:Monad m}.

  Definition state_t_ret {S A} (a:A) : state_t S m A := StateT $ fun s => ret (a,s).
  Definition state_t_bind {S A B} (aM:state_t S m A) (f:A -> state_t S m B) : state_t S m B :=
    StateT $ fun s => begin
      as' <- un_state_t aM s ;;
      let (a,s') := as' in
      un_state_t (f a) s'
    end.
  Global Instance state_t_Monad {S} : Monad (state_t S m) :=
    { ret := @state_t_ret _
    ; bind := @state_t_bind _
    }.

  Definition state_t_get {S} : state_t S m S :=
    StateT $ fun s => ret (s,s).
  Definition state_t_put {S} (s:S) : state_t S m unit :=
    StateT $ fun _ => ret (tt,s).
  Global Instance state_t_MonadState {S} : MonadState S (state_t S m) :=
    { get := @state_t_get _
    ; put := @state_t_put _
    }.
  
End state_t.

Definition state S := state_t S identity.
Definition run_state {S A} : S -> state S A -> (A*S) := run_identity <..> run_state_t.
Definition eval_state {S A} : S -> state S A -> A := run_identity <..> eval_state_t.
Definition exec_state {S A} : S -> state S A -> S := run_identity <..> exec_state_t.
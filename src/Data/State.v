Require Import FP.Classes.
Require Import FP.CoreData.
Require Import FP.Data.Type.
Require Import FP.Data.Identity.

Import ClassesNotation.
Import CoreDataNotation.

Inductive state_t S m A := StateT { un_state_t : S -> m (A * S) }.
Arguments StateT {S m A} _.
Arguments un_state_t {S m A} _ _.

Definition run_state_t {S m A} : S -> state_t S m A -> m (A * S) := flip un_state_t.

Definition state S := state_t S identity.
Definition run_state {S A} : S -> state S A -> (A * S) := run_identity '.:' run_state_t.

Section Monad.
  Context {S:Type} {m} `{! Monad m }.

  Definition state_t_mret {A} (a:A) : state_t S m A := StateT $ fun s => mret (a, s).
  Definition state_t_mbind {A B} (aM:state_t S m A) (k:A -> state_t S m B) : state_t S m B :=
    StateT $ fun s =>
      axs' <- run_state_t s aM ;;
      let (a,s') := axs' in
      run_state_t s' $ k a.
  Global Instance state_t_Monad : Monad (state_t S m) :=
    { mret := @state_t_mret
    ; mbind := @state_t_mbind
    }.

  Definition state_t_mget : state_t S m S := StateT $ fun s => mret (s, s).
  Definition state_t_mput (s:S) : state_t S m unit := StateT $ const (mret (tt, s)).
  Global Instance state_t_MonadState : MonadState S (state_t S m) :=
    { mget := state_t_mget
    ; mput := state_t_mput
    }.
End Monad.

Definition eval_state_t {S m A} `{! Monad m } : S -> state_t S m A -> m A := mbind_fmap fst '.:' run_state_t.
Definition exec_state_t {S m A} `{! Monad m } : S -> state_t S m A -> m S := mbind_fmap snd '.:' run_state_t.

Definition eval_state {S A} : S -> state S A -> A := run_identity '.:' eval_state_t.
Definition exec_state {S A} : S -> state S A -> S := run_identity '.:' exec_state_t.
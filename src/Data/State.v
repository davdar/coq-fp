Require Import FP.Categories.
Require Import FP.CoreData.
Require Import FP.Data.Type.
Require Import FP.Data.Identity.

Import CategoriesNotation.
Import CoreDataNotation.

Inductive state_t S m A := StateT { un_state_t : S -> m (A * S) }.
Arguments StateT {S m A} _.
Arguments un_state_t {S m A} _ _.

Definition run_state_t {S m A} : S -> state_t S m A -> m (A * S) := flip un_state_t.

Definition state S := state_t S identity.
Definition run_state {S A} : S -> state S A -> (A * S) := run_identity '.:' run_state_t.

Section Monad.
  Context {S:Type} {m} `{! FUnit m ,! MBind m }.

  Definition state_t_funit {A} (a:A) : state_t S m A := StateT $ fun s => ret (a, s).
  Global Instance state_t_FUnit : FUnit (state_t S m) :=
    { funit := @state_t_funit }.

  Definition state_t_bind {A B} (aM:state_t S m A) (k:A -> state_t S m B) : state_t S m B :=
    StateT $ fun s =>
      axs' <- run_state_t s aM ;;
      let (a,s') := axs' in
      run_state_t s' $ k a.
  Global Instance state_t_MBind : MBind (state_t S m) :=
    { bind := @state_t_bind }.

  Definition state_t_get : state_t S m S := StateT $ fun s => ret (s, s).
  Definition state_t_put (s:S) : state_t S m unit := StateT $ const (ret (tt, s)).
  Global Instance state_t_MonadState : MonadState S (state_t S m) :=
    { get := state_t_get
    ; put := state_t_put
    }.
End Monad.

Definition eval_state_t {S m A} `{! FUnit m ,! MBind m } : S -> state_t S m A -> m A := bind_fmap fst '.:' run_state_t.
Definition exec_state_t {S m A} `{! FUnit m ,! MBind m } : S -> state_t S m A -> m S := bind_fmap snd '.:' run_state_t.

Definition eval_state {S A} : S -> state S A -> A := run_identity '.:' eval_state_t.
Definition exec_state {S A} : S -> state S A -> S := run_identity '.:' exec_state_t.
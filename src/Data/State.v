Require Import FP.Data.Function.
Require Import FP.Data.Prod.
Require Import FP.Data.Type.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Monad.
Require Import FP.Structures.Multiplicative.
Require Import FP.Structures.MonadState.
Require Import FP.Structures.MonadError.
Require Import FP.Structures.MonadTrans.
Require Import FP.Structures.MonadPlus.
Require Import FP.Structures.Alternative.
Require Import FP.Data.Identity.

Import FunctionNotation.
Import FunctorNotation.
Import MonadNotation.
Import MultiplicativeNotation.
Import AlternativeNotation.

Inductive state_t S m A := StateT { un_state_t : S -> m (A * S) }.
Arguments StateT {S m A} _.
Arguments un_state_t {S m A} _ _.


Section MonadTrans.
  Context {S:Type}.

  Definition state_t_lift {m} {M:Monad m} {A} (aM:m A) : state_t S m A :=
    StateT $ fun s => fmap (flip pair s) aM.
  Global Instance state_t_MonadTrans : MonadTrans (state_t S) :=
    { lift  := @state_t_lift }.
End MonadTrans.

Section state_t.
  Context {S:Type} {m} {M:Monad m}.

  Definition run_state_t {A} : S -> state_t S m A -> m (A * S) := flip un_state_t.
  Definition eval_state_t {A} : S -> state_t S m A -> m A := fmap fst '..' run_state_t.
  Definition exec_state_t {A} : S -> state_t S m A -> m S := fmap snd '..' run_state_t.

  Definition state_t_ret {A} (a:A) : state_t S m A := StateT $ fun s => ret (a,s).
  Definition state_t_bind {A B} (aM:state_t S m A) (f:A -> state_t S m B) : state_t S m B :=
    StateT $ fun s => begin
      as' <- un_state_t aM s ;;
      let (a,s') := as' in
      un_state_t (f a) s'
    end.
  Global Instance state_t_Monad : Monad (state_t S m) :=
    { ret := @state_t_ret 
    ; bind := @state_t_bind 
    }.

  Definition state_t_get : state_t S m S :=
    StateT $ fun s => ret (s,s).
  Definition state_t_put (s:S) : state_t S m unit :=
    StateT $ fun _ => ret (tt,s).
  Global Instance state_t_MonadState : MonadState S (state_t S m) :=
    { get := @state_t_get
    ; put := @state_t_put
    }.

  Section MonadError.
    Context {E} {ME:MonadError E m}.

    Definition state_t_throw {A} : E -> state_t S m A := lift '.' throw.
    Definition state_t_catch {A}
        (aM:state_t S m A) (h:E -> state_t S m A) : state_t S m A :=
      StateT $ fun s => catch (un_state_t aM s) $ run_state_t s '.' h.
    Global Instance state_t_MonadError : MonadError E (state_t S m) :=
      { throw := @state_t_throw
      ; catch := @state_t_catch
      }.
  End MonadError.

  Section MonadPlus.
    Context {MP:MonadPlus m}.

    Definition state_t_mzero {A} : state_t S m A := lift mzero.
    Definition state_t_mplus {A B}
        (aM:state_t S m A) (bM:state_t S m B) : state_t S m (A+B) :=
      StateT $ fun s =>
        r <- un_state_t aM s <+> un_state_t bM s ;;
        ret $
          match r with
          | inl (a,s) => (inl a,s)
          | inr (b,s) => (inr b,s)
          end.
    Global Instance state_t_MonadPlus : MonadPlus (state_t S m) :=
      { mzero := @state_t_mzero
      ; mplus := @state_t_mplus
      }.
  End MonadPlus.
End state_t.

Definition state S := state_t S identity.
Definition run_state {S A} : S -> state S A -> (A*S) := run_identity '..' run_state_t.
Definition eval_state {S A} : S -> state S A -> A := run_identity '..' eval_state_t.
Definition exec_state {S A} : S -> state S A -> S := run_identity '..' exec_state_t.
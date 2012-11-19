Require Import Structures.Monad.
Require Import Structures.MonadCont.
Require Import Structures.MonadTrans.
Require Import Data.Function.
Require Import Data.Identity.

Import FunctionNotation.
Import MonadNotation.

Inductive cont_t R (m:Type -> Type) A := ContT { un_cont_t : (A -> m R) -> m R }.
Arguments ContT {R m A} _.
Arguments un_cont_t {R m A} _ _.

Definition run_cont_t {m} {M:Monad m} {A} (c:cont_t A m A) : m A :=
  un_cont_t c ret.

Definition cont_t_ret {R} {m} {M:Monad m} {A} : A -> cont_t R m A :=
  ContT <.> apply_to.
Definition cont_t_bind {R} {m} {M:Monad m} {A B}
    (aM:cont_t R m A) (f:A -> cont_t R m B) : cont_t R m B :=
  ContT $ fun (k:B -> m R) =>
    un_cont_t aM $ fun (a:A) =>
      un_cont_t (f a) $ fun (b:B) =>
        k b.

Instance cont_t_Monad {R} {m} {M:Monad m} : Monad (cont_t R m) :=
  { ret := @cont_t_ret _ _ _
  ; bind := @cont_t_bind _ _ _
  }.

Definition cont_t_lift {R} {m} {M:Monad m} {A} (aM:m A) : cont_t R m A :=
  ContT $ fun (k:A -> m R) => aM >>= k.

Instance cont_t_MonadTrans {R} : MonadTrans (cont_t R) :=
  { lift := @cont_t_lift _ }.

Definition cont_t_callcc {R} {m} {M:Monad m} {A}
    (kk:(A -> cont_t R m R) -> cont_t R m R) : cont_t R m A :=
  ContT $ fun (k:A -> m R) =>
    run_cont_t $
      kk $ fun (a:A) =>
        ContT $ fun (kR:R -> m R) =>
          k a >>= kR.

Instance cont_t_MoandCont {R} {m} {M:Monad m} : MonadCont R (cont_t R m) :=
  { callcc := @cont_t_callcc _ _ _ }.

Definition cont R := cont_t R identity.
Definition mk_cont {A R} (kk:(A -> R) -> R) : cont R A :=
  ContT $ fun k => Identity $ kk $ run_identity <.> k.
Definition run_cont {A} : cont A A -> A :=
  run_identity <.> run_cont_t.
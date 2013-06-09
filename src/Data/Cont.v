Require Import FP.Classes.
Require Import FP.CoreData.
Require Import FP.Data.Identity.

Import CoreDataNotation.
Import ClassesNotation.

Inductive cont_t R (m:Type -> Type) A := ContT { un_cont_t : (A -> m R) -> m R }.
Arguments ContT {R m A} _.
Arguments un_cont_t {R m A} _ _.

Section cont_t.
  Context {m} `{! Monad m }.

  Definition run_cont_t {A} (c:cont_t A m A) : m A := un_cont_t c mret.

  Context {R:Type}.

  Definition cont_t_mret {A} : A -> cont_t R m A := ContT '.' apply_to.
  Definition cont_t_mbind {A B} (aM:cont_t R m A) (f:A -> cont_t R m B) : cont_t R m B :=
    ContT $ fun (k:B -> m R) =>
      un_cont_t aM $ fun (a:A) =>
        un_cont_t (f a) $ fun (b:B) =>
          k b.
  Global Instance cont_t_Monad : Monad (cont_t R m) :=
    { mret := @cont_t_mret
    ; mbind := @cont_t_mbind
    }.

  Definition cont_t_callcc {A} (kk:(A -> cont_t R m R) -> cont_t R m R) : cont_t R m A :=
    ContT $ fun (k:A -> m R) =>
      run_cont_t $
        kk $ fun (a:A) =>
          ContT $ fun (kR:R -> m R) =>
            k a >>= kR.
  Global Instance cont_t_MoandCont : MonadCont R (cont_t R m) := { callcc := @cont_t_callcc }.
End cont_t.

Definition cont R := cont_t R identity.
Definition mk_cont {A R} (kk:(A -> R) -> R) : cont R A :=
  ContT $ fun k => Identity $ kk $ run_identity '.' k.
Definition run_cont {A} : cont A A -> A :=
  run_identity '.' run_cont_t.
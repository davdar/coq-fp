Require Import FP.Data.Function.
Require Import FP.Data.Identity.
Require Import FP.Data.Reader.
Require Import FP.Data.Type.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadDelay.
Require Import FP.Structures.Multiplicative.

Import MonadNotation.
Import ComonadNotation.
Import FunctionNotation.
Import MultiplicativeNotation.

Inductive susp_t (m:Type -> Type) A := SuspT { un_susp_t : unit -> m A }.
Arguments SuspT {m A} _.
Arguments un_susp_t {m A} _ _.

Definition run_susp_t {m A} : susp_t m A -> m A := apply_to tt '.' un_susp_t.

Local Notation "'delay_t' | e" := (SuspT (fun _ => e)) (at level 105).
Definition force_t {m A} : susp_t m A -> m A := run_susp_t.

Definition susp_t_ret {m} {M:Monad m} {A} (a:A) : susp_t m A :=
  delay_t | ret a.
Definition susp_t_bind {m} {M:Monad m} {A B}
    (aM:susp_t m A) (f:A -> susp_t m B) : susp_t m B :=
  delay_t | a <- force_t aM ;; force_t $ f a.

Instance susp_Monad {m} {M:Monad m} : Monad (susp_t m) :=
  { ret := @susp_t_ret _ _
  ; bind := @susp_t_bind _ _
  }.

Definition susp_t_coret {m} {M:Comonad m} {A} : susp_t m A -> A :=
  coret '.' run_susp_t.
Definition susp_t_cobind {m} {M:Comonad m} {A B}
    (aMM:susp_t m A) (f:susp_t m A -> B) : susp_t m B :=
  delay_t | codo aM -< force_t aMM => f (delay_t | aM).

Instance susp_Comonad {m} {M:Comonad m} : Comonad (susp_t m) :=
  { coret := @susp_t_coret _ _
  ; cobind := @susp_t_cobind _ _
  }.

Definition susp := susp_t identity.
Definition run_susp {A} : susp A -> A := run_identity '.' run_susp_t.

Local Notation "'delay' | e" := (SuspT (fun _ => Identity e)) (at level 105).
Definition force {A} : susp A -> A := run_susp.

Module SuspNotation.
  Notation "'delay_t' | e" := (SuspT (fun _ => e)) (at level 105).
  Notation "'delay' | e" := (SuspT (fun _ => Identity e)) (at level 105).
End SuspNotation.

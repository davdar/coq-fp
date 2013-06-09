Require Import FP.CoreData.
Require Import FP.Classes.
Require Import FP.Data.Identity.

Import CoreDataNotation.
Import ClassesNotation.

Inductive susp_t (w:Type -> Type) (A:Type) : Type := SuspT
  { un_susp_t : unit -> w A }.
Arguments SuspT {w A} _.
Arguments un_susp_t {w A} _ _.

Section susp_t.
  Context {m:Type->Type}.

  Definition run_susp_t {A} : susp_t m A -> m A := apply_to tt '.' un_susp_t.
  Definition force_t {A} : susp_t m A -> m A := run_susp_t.
End susp_t.

Definition susp := susp_t identity.
Definition run_susp {A} : susp A -> A := run_identity '.' run_susp_t.
Definition force {A} : susp A -> A := run_susp.

Module SuspNotation.
  Notation "'delay_t' | e" := (SuspT (fun _ => e)) (at level 105).
  Notation "'delay' | e" := (SuspT (fun _ => Identity e)) (at level 105).
End SuspNotation.
Import SuspNotation.

Section Monad.
  Context {m} `{! Monad m }.

  Definition susp_t_mret {A} (a:A) : susp_t m A := delay_t | mret a.
  Definition susp_t_mbind {A B} (aM:susp_t m A) (f:A -> susp_t m B) : susp_t m B :=
    delay_t | a <- force_t aM ;; force_t $ f a.
  Global Instance susp_t_Monad : Monad (susp_t m) :=
    { mret := @susp_t_mret
    ; mbind := @susp_t_mbind
    }.
End Monad.

Section Comonad.
  Context {w} `{! Comonad w }.

  Definition susp_t_coret {A} : susp_t w A -> A := coret '.' run_susp_t.
  Definition susp_t_cobind {A B} (aMM:susp_t w A) (f:susp_t w A -> B) : susp_t w B :=
    delay_t | codo aM -< force_t aMM => f (delay_t | aM).
  Global Instance susp_t_Cobind : Comonad (susp_t w) :=
    { coret := @susp_t_coret
    ; cobind := @susp_t_cobind
    }.
End Comonad.
Require Import Data.FunctionPre.

Require Import Data.Identity.
Require Import Data.Reader.
Require Import Data.Type.
Require Import Structures.Comonad.
Require Import Structures.Injection.
Require Import Structures.Monad.
Require Import Structures.MonadDelay.
Require Import Structures.Multiplicative.

Import MonadNotation.
Import ComonadNotation.
Import FunctionNotation.
Import MultiplicativeNotation.

Inductive susp_t (m:Type -> Type) A := SuspT { un_susp_t : unit -> m A }.
Arguments SuspT {m A} _.
Arguments un_susp_t {m A} _ _.

Definition run_susp_t {m A} : susp_t m A -> m A := apply_to tt <.> un_susp_t.

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
  coret <.> run_susp_t.
Definition susp_t_cobind {m} {M:Comonad m} {A B}
    (aMM:susp_t m A) (f:susp_t m A -> B) : susp_t m B :=
  delay_t | codo aM -< force_t aMM => f (delay_t | aM).

Instance susp_Comonad {m} {M:Comonad m} : Comonad (susp_t m) :=
  { coret := @susp_t_coret _ _
  ; cobind := @susp_t_cobind _ _
  }.

Definition susp := susp_t identity.
Definition run_susp {A} : susp A -> A := run_identity <.> run_susp_t.

Local Notation "'delay' | e" := (SuspT (fun _ => Identity e)) (at level 105).
Definition force {A} : susp A -> A := run_susp.

Module SuspNotation.
  Notation "'delay_t' | e" := (SuspT (fun _ => e)) (at level 105).
  Notation "'delay' | e" := (SuspT (fun _ => Identity e)) (at level 105).
End SuspNotation.

(*
Inductive delay_t m (A:Type) := DelayT { un_delay_t : unit -> m A }.
Arguments DelayT {m A} _.
Arguments un_delay_t {m A} _ _.

Definition run_delay_t {m A} : delay_t m A -> m A := apply_to tt <.> un_delay_t.

(*
Definition delay_t_bind {m} {M:Monad m} {A B} (aMM:delay_t m A) (f:A -> delay_t m B) : delay_t m B :=
  DelayT $ ReaderT $ fun _ =>
    a <- run_delay_t aMM ;;
    run_delay_t $ f a.
*)

Definition delay_t_ret {m} {M:Monad m} {A} (a:A) : delay_t m A := DelayT $ fun _ => ret a.
Definition delay_t_bind {m} {M:Monad m} {A B} (aMM:delay_t m A) (f:A -> delay_t m B) : delay_t m B :=
  DelayT $ begin
    a <- un_delay_t aMM tt ;;
    let x := un_delay_t $ f a in
    
  end.

Instance delay_t_Monad {m} {M:Monad m} : Monad (delay_t m) := iso_Monad (reader_t unit m).

Definition delay_t_force {m} {M:Monad m} {A} (aMM:delay_t m A) : delay_t m A :=
  let aM := run_delay_t aMM in mk_delay_t (fun _ => aM).
Instance delay_t_MonadDelay {m} {M:Monad m} : MonadDelay (delay_t m) :=
  { force := @delay_t_force _ _ }.

Definition delay := delay_t identity.
Definition run_delay {A} : delay A -> A := run_identity <.> run_delay_t.
Definition mk_delay {A} : (unit -> A) -> delay A := mk_delay_t <.> compose Identity.

(*
Inductive delay_t2 (m:Type -> Type) A := DelayT2 { un_delay_t2 : { B : Type & B * (B -> m A) }}.
Arguments DelayT2 {m A} _.
Arguments un_delay_t2 {m A} _.

Print sigT.

Definition delay_t2_ret {m} {M:Monad m} {A} (a:A) : delay_t2 m A :=
  DelayT2 $ existT _ _ (a, ret <.> id).

Definition delay_t2_bind {m} {M:Monad m} {A B} (aMM:delay_t2 m A) (f:A -> delay_t2 m B) : delay_t2 m B :=
  let '(existT _ e k) := aMM in
    DelayT2 $ existT _ _ (fun _ => ... , apply tt)
  a <- k e ;;
  f a
  match un_delay_t2 with
  | 
*)
*)
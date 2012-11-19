Require Import Structures.Comonad.
Require Import Data.FunctionPre.
Require Import Data.Identity.
Require Import Data.Susp.
Require Import Structures.Monad.
Require Import Data.Cont.
Require Import Structures.MonadCont.
Require Import Structures.MonadState.

Import FunctionNotation.
Import SuspNotation.
Import MonadNotation.

Class Peano T :=
  { pzero : T
  ; psucc : T -> T
  }.

Definition pinc {m} {M:Monad m} {T} {P:Peano T} {MS:MonadState T m} : m T :=
  p <- get ;;
  modify psucc ;;
  ret p.

Definition Coiter m T {A} := (m A -> A) -> m A -> T -> A.

Definition mk_iter {T A} (coiter:Coiter identity T) (f:A -> A) (a:A) : T -> A :=
  coiter (f <.> run_identity) (Identity a).

Definition mk_miter {m} {M:Monad m} {T A}
    (coiter:Coiter identity T) (f:A -> m A) (a:A) : T -> m A :=
  mk_iter coiter (revbind f) (ret a).

Definition mk_lazyiter {T A}
    (coiter:Coiter susp T) (f:forall {C}, (C -> A) -> C -> A) (a:A) : T -> A :=
  coiter (fun (aM:susp A) => f coret aM) (delay | a).

Class PeanoR T :=
  { coiterr : forall {m} {M:Comonad m} {A}, (m A -> A) -> m A -> T -> A }.

Definition iterr {T} {P:PeanoR T} {A}
  : (A -> A) -> A -> T -> A := mk_iter coiterr.

Definition miterr {T} {P:PeanoR T} {m} {M:Monad m} {A}
  : (A -> m A) -> A -> T -> m A := mk_miter coiterr.

Definition lazyiterr {T} {P:PeanoR T} {A}
  : (forall {C}, (C -> A) -> C -> A) -> A -> T -> A := mk_lazyiter coiterr.

Definition iter_fix {T} {P:PeanoR T} {A B} (ff:(A -> option B) -> A -> option B) : T -> A -> option B :=
  lazyiterr (fun _ k l => ff $ fun a => k l a) (const None).

Definition iter_mfix {m} {M:Monad m} {T} {P:PeanoR T} {A B}
    (ff:(A -> m (option B)) -> A -> m (option B)) : T -> A -> m (option B) :=
  lazyiterr (fun _ k l => ff $ fun a => k l a) (const $ ret None).

Class PeanoL T :=
  { coiterl : forall {m} {M:Comonad m} {A}, (m A -> A) -> m A -> T -> A }.

Definition iterl {T} {P:PeanoL T} {A}
  : (A -> A) -> A -> T -> A := mk_iter coiterl.

Definition miterl {T} {P:PeanoL T} {m} {M:Monad m} {A}
  : (A -> m A) -> A -> T -> m A := mk_miter coiterl.

Definition lazyiterl {T} {P:PeanoL T} {A}
  : (forall {C}, (C -> A) -> C -> A) -> A -> T -> A := mk_lazyiter coiterl.

Require Import FP.Structures.Comonad.
Require Import FP.Data.Function.
Require Import FP.Data.Identity.
Require Import FP.Data.Susp.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadState.
Require Import FP.Structures.Counit.
Require Import FP.Structures.Comonad.
Require Import FP.Data.Cont.
Require Import FP.Structures.MonadCont.
Require Import FP.Structures.MonadState.

Import FunctionNotation.
Import SuspNotation.
Import MonadNotation.

Class Peano T :=
  { pzero : T
  ; psucc : T -> T
  ; coloopr : forall {m} {M:Comonad m} {A}, (m A -> A) -> m A -> T -> A
  ; coloopl : forall {m} {M:Comonad m} {A}, (m A -> A) -> m A -> T -> A
  }.

Section pinc.
  Context {m} {Monad_:Monad m} {T} {Peano_:Peano T} {MState_:MState T m}. 
  Definition pinc : m T :=
    p <- get ;;
    modify psucc ;;
    ret p.
End pinc.

Definition Coloop m T {A} := (m A -> A) -> m A -> T -> A.

Definition mk_loop {T A} (coloop:Coloop identity T) (f:A -> A) (a:A) : T -> A :=
  coloop (f '.' run_identity) (Identity a).

Definition mk_mloop {m} {M:Monad m} {T A}
    (coloop:Coloop identity T) (f:A -> m A) (a:A) : T -> m A :=
  mk_loop coloop (extend f) (ret a).

Definition mk_lazyloop {T A}
    (coloop:Coloop susp T) (f:forall {C}, (C -> A) -> C -> A) (a:A) : T -> A :=
  coloop (fun (aM:susp A) => f coret aM) (delay | a).

Definition loopr {T} {P:Peano T} {A}
  : (A -> A) -> A -> T -> A := mk_loop coloopr.

Definition miterr {T} {P:Peano T} {m} {M:Monad m} {A}
  : (A -> m A) -> A -> T -> m A := mk_mloop coloopr.

Definition lazyiterr {T} {P:Peano T} {A}
  : (forall {C}, (C -> A) -> C -> A) -> A -> T -> A := mk_lazyloop coloopr.

Definition loopr_fix {T} {P:Peano T} {A B} (ff:(A -> option B) -> A -> option B)
    : T -> A -> option B :=
  lazyiterr (fun _ k l => ff $ fun a => k l a) (const None).

Definition loopr_mfix {m} {M:Monad m} {T} {P:Peano T} {A B}
    (ff:(A -> m (option B)) -> A -> m (option B)) : T -> A -> m (option B) :=
  lazyiterr (fun _ k l => ff $ fun a => k l a) (const $ ret None).

Definition loopl {T} {P:Peano T} {A}
  : (A -> A) -> A -> T -> A := mk_loop coloopl.

Definition mloopl {T} {P:Peano T} {m} {M:Monad m} {A}
  : (A -> m A) -> A -> T -> m A := mk_mloop coloopl.

Definition lazyloopl {T} {P:Peano T} {A}
  : (forall {C}, (C -> A) -> C -> A) -> A -> T -> A := mk_lazyloop coloopl.
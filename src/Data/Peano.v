Require Import FP.Categories.
Require Import FP.CoreData.
Require Import FP.Data.Identity.
Require Import FP.Data.Susp.

Import CoreDataNotation.
Import CategoriesNotation.
Import SuspNotation.

Section pinc.
  Context {m T} `{! FUnit m ,! MBind m ,! MonadState T m ,! Peano T }.

  Definition pinc : m T :=
    p <- get ;;
    modify psucc ;;
    ret p.
End pinc.

(* generic loop creators, to be instantiated with both loopl and loopr *)
Definition coloop_t m T {A} := (m A -> A) -> m A -> T -> A.

Definition mk_loop {T A} (coloop:coloop_t identity T) (f:A -> A) (a:A) : T -> A :=
  coloop (f '.' run_identity) (Identity a).

Definition mk_mloop {m T A} `{! FUnit m ,! MBind m }
    (coloop:coloop_t identity T) (f:A -> m A) (a:A) : T -> m A :=
  mk_loop coloop (extend f) (ret a).

Definition mk_lazyloop {T A}
    (coloop:coloop_t susp T) (f:forall {C}, (C -> A) -> C -> A) (a:A) : T -> A :=
  coloop (fun (aM:susp A) => f coret aM) (delay | a).

Definition loopr {T} {P:Peano T} {A} : (A -> A) -> A -> T -> A := mk_loop coloopr.

Definition mloopr {T m A} `{! Peano T ,! FUnit m ,! MBind m }
  : (A -> m A) -> A -> T -> m A := mk_mloop coloopr.

Definition lazy_loopr {T A} `{! Peano T }
  : (forall {C}, (C -> A) -> C -> A) -> A -> T -> A := mk_lazyloop coloopr.

Definition loopr_fix {T A B} `{! Peano T } (ff:(A -> option B) -> A -> option B)
    : T -> A -> option B :=
  lazy_loopr (fun _ k l => ff $ fun a => k l a) (const None).

Definition loopr_mfix {m T A B} `{! FUnit m ,! MBind m ,! Peano T }
    (ff:(A -> m (option B)) -> A -> m (option B)) : T -> A -> m (option B) :=
  lazy_loopr (fun _ k l => ff $ fun a => k l a) (const $ ret None).

Definition loopl {T A} `{! Peano T }
  : (A -> A) -> A -> T -> A := mk_loop coloopl.

Definition mloopl {T m A} `{! Peano T ,! FUnit m ,! MBind m }
  : (A -> m A) -> A -> T -> m A := mk_mloop coloopl.

Definition lazy_loopl {T A} `{! Peano T }
  : (forall {C}, (C -> A) -> C -> A) -> A -> T -> A := mk_lazyloop coloopl.
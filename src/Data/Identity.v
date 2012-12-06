Require Import FP.Data.Function.
Require Import FP.Structures.Monad.
Require Import FP.Structures.Comonad.

Import FunctionNotation.

Inductive identity A := Identity { un_identity : A }.
Arguments Identity {A} _.
Arguments un_identity {A} _.

Definition run_identity {A} : identity A -> A := un_identity.

Definition identity_ret {A} : A -> identity A := Identity.
Definition identity_bind {A B} (aM:identity A) (f:A -> identity B) : identity B :=
  f $ un_identity aM.
Instance identity_Monad : Monad identity :=
  { ret := @identity_ret
  ; bind := @identity_bind
  }.

Definition identity_coret {A} : identity A -> A := un_identity.
Definition identity_cobind {A B} (aM:identity A) (f:identity A -> B) : identity B :=
  Identity $ f aM.
Instance identity_Comonad : Comonad identity :=
  { coret := @identity_coret
  ; cobind := @identity_cobind
  }.

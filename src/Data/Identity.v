Require Import FP.Data.Function.
Require Import FP.Structures.FUnit.
Require Import FP.Structures.Counit.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Monad.
Require Import FP.Structures.Comonad.

Import FunctionNotation.

Inductive identity A := Identity { un_identity : A }.
Arguments Identity {A} _.
Arguments un_identity {A} _.

Definition run_identity {A} : identity A -> A := un_identity.

Definition identity_funit {A} : A -> identity A := Identity.
Instance identity_FUnit : FUnit identity :=
  { funit := @identity_funit }.

Definition identity_bind {A B} (aM:identity A) (f:A -> identity B) : identity B :=
  f $ un_identity aM.
Instance identity_Bind : MBind identity :=
  { bind := @identity_bind}.

Definition identity_counit {A} : identity A -> A := un_identity.
Instance identity_Counit : Counit identity :=
  { counit := @identity_counit }.

Definition identity_cobind {A B} (aM:identity A) (f:identity A -> B) : identity B :=
  Identity $ f aM.
Instance identity_CoMBind : Cobind identity :=
  { cobind := @identity_cobind }.

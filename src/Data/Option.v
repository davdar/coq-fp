Require Export Coq.Init.Datatypes.

Require Import Data.Function.
Require Import Data.String.
Require Import Structures.Injection.
Require Import Structures.Monad.
Require Import Structures.MonadFail.

Import FunctionNotation.

Section MonadFail.
  Context {m e} {M:Monad m} {F:MonadFail e m} {I:Injection string e}.

  Definition fail_option {A} (msg:string) (xM:option A) : m A :=
    match xM with
    | None => throw $ inject msg
    | Some x => ret x
    end.
End MonadFail.

Inductive option_t m (A:Type) := OptionT { un_option_t : option (m A) }.

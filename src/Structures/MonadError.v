Require Import Data.FunctionPre.
Require Import Data.StringPre.

Require Import Structures.Injection.

Import FunctionNotation.

Class MonadError E (m:Type -> Type) :=
{ throw : forall {A}, E -> m A
; catch : forall {A}, m A -> (E -> m A) -> m A
}.

Section iso_MonadError.
  Context {m} {n} {B:FunctorBijection m n} {E} {nME:MonadError E n}.
  Definition iso_MonadError_throw {A} : E -> m A := ffrom <.> throw.
  Definition iso_MonadError_catch {A} (aM:m A) (h:E -> m A) : m A :=
    ffrom $ catch (fto aM) (fto <.> h).
End iso_MonadError.
Definition iso_MonadError {m} n {B:FunctorBijection m n} {E} {nMR:MonadError E n} : MonadError E m :=
  {| throw := @iso_MonadError_throw _ _ _ _ _
   ; catch := @iso_MonadError_catch _ _ _ _ _
  |}.

Definition catch_with {E} {m} {ME:MonadError E m} {A} : (E -> m A) -> m A -> m A := flip catch.

Section throw_msg.
  Context {m E} {ME:MonadError E m} {I:Injection string E}.

  Definition throw_msg {A} : string -> m A := throw <.> inject.
End throw_msg.

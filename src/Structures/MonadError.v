Require Import FP.Data.Function.
Require Import FP.Data.StringPre.
Require Import FP.Structures.Injection.

Import FunctionNotation.

Class MonadError E (m:Type -> Type) :=
  { throw : forall {A}, E -> m A
  ; catch : forall {A}, m A -> (E -> m A) -> m A
  }.

Section MonadError.
  Context {m E} {m_MonadError : MonadError E m}.

  Definition catch_with {A} : (E -> m A) -> m A -> m A := flip catch.

  Context {e_Injection : Injection string E}.

  Definition throw_msg {A} : string -> m A := throw '.' inject.
End MonadError.

Section iso_MonadError.
  Variable n:Type -> Type.
  Context {m} {B:FunctorBijection m n} {E} {nME:MonadError E n}.
  Definition iso_MonadError_throw {A} : E -> m A := ffrom '.' throw.
  Definition iso_MonadError_catch {A} (aM:m A) (h:E -> m A) : m A :=
    ffrom $ catch (fto aM) (fto '.' h).
  Definition iso_MonadError : MonadError E m :=
    {| throw := @iso_MonadError_throw
     ; catch := @iso_MonadError_catch
    |}.
End iso_MonadError.
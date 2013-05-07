Require Import FP.Data.Error.
Require Import FP.Categories.
Require Import FP.CoreData.
Require Import FP.CoreClasses.

Import CoreDataNotation.
Import CategoriesNotation.

Inductive error_t E m A := ErrorT { un_error_t : m (Error E A) }.
Arguments ErrorT {E m A} _.
Arguments un_error_t {E m A} _.

Section Monad.
  Context {m} {E:Type} `{! Monad m }.

  Definition error_t_unit {A} (a:A) : error_t E m A := ErrorT $ ret $ Success a.
  Global Instance error_t_FUnit : FUnit (error_t E m) := { funit := @error_t_unit }.

  Definition error_t_bind {A B} (aMM:error_t E m A) (k:A -> error_t E m B) : error_t E m B :=
    ErrorT begin
      aM <- un_error_t aMM ;;
      match aM with
      | Failure e => ret $ Failure e
      | Success a => un_error_t $ k a
      end
    end.
  Global Instance error_t_MBind : MBind (error_t E m) := { bind := @error_t_bind }.

  Context `{! Eqv E ,! FEqv m ,! MonadWF m }.

  Global Instance error_t_MonadWF : MonadWF (error_t E m).
End Monad.
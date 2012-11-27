Require Import FP.Data.FunctionPre.

Require Import FP.Structures.Alternative.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadError.
Require Import FP.Structures.MonadFix.
Require Import FP.Structures.MonadPlus.
Require Import FP.Structures.MonadReader.
Require Import FP.Structures.MonadTrans.
Require Import FP.Structures.MonadState.

Import AlternativeNotation.
Import FunctionNotation.
Import MonadNotation.

Inductive reader_t R (m:Type -> Type) A := ReaderT { un_reader_t : R -> m A }.
Arguments ReaderT {R m A} _.
Arguments un_reader_t {R m A} _ _.

Section MonadTrans.
  Context {R:Type}.

  Definition reader_t_lift {m} {M:Monad m} {A} (aM:m A) : reader_t R m A :=
    ReaderT $ fun r => aM.
  Global Instance reader_t_MonadTrans : MonadTrans (reader_t R) :=
    { lift  := @reader_t_lift }.
End MonadTrans.

Section reader_t.
  Context {R:Type} {m} {M:Monad m}.

  Definition run_reader_t {A} : R -> reader_t R m A -> m A := flip un_reader_t.

  Section Monad.
    Definition reader_t_ret {A} : A -> reader_t R m A := ReaderT <.> const <.> ret.
    Definition reader_t_bind {A B}
        (aMM:reader_t R m A) (f:A -> reader_t R m B) : reader_t R m B :=
      ReaderT $ fun r => begin
        a <- un_reader_t aMM r ;;
        un_reader_t (f a) r
      end.
    Global Instance reader_t_Monad : Monad (reader_t R m) :=
      { ret := @reader_t_ret
      ; bind := @reader_t_bind
      }.
  End Monad.

  Section MonadReader.
    Definition reader_t_ask : reader_t R m R :=
      ReaderT $ fun r => ret r.
    Definition reader_t_local {A} (f:R -> R) (aM: reader_t R m A) : reader_t R m A :=
      ReaderT $ fun r => un_reader_t aM (f r).
    Global Instance reader_t_MonadReader : MonadReader R (reader_t R m) :=
      { ask := @reader_t_ask
      ; local := @reader_t_local
      }.
  End MonadReader.

  Section ReaderT_passthrough.
    Context {R2} {MR2:MonadReader R2 m}.

    Definition reader_t_ask_passthrough : reader_t R m R2 := lift ask.
    Definition reader_t_local_passthrough {A} (f:R2 -> R2) (aM:reader_t R m A) :=
      ReaderT $ local f <.> un_reader_t aM.
    Definition reader_t_MonadReader_passthrough : MonadReader R2 (reader_t R m) :=
      {| ask := @reader_t_ask_passthrough
       ; local := @reader_t_local_passthrough
      |}.                                          
  End ReaderT_passthrough.

  Section MonadState.
    Context {S} {MS:MonadState S m}.

    Definition reader_t_get : reader_t R m S := lift get.
    Definition reader_t_put : S -> reader_t R m unit :=lift <.> put.
    Global Instance reader_t_MonadState : MonadState S (reader_t R m) :=
      { get := reader_t_get
      ; put := reader_t_put
      }.
  End MonadState.

  Section MonadFix.
    Context {MF:MonadFix m}.

    Definition reader_t_mfix {A B}
        (ff:(A -> reader_t R m B) -> A -> reader_t R m B) (a:A) : reader_t R m B :=
      let ff' (f':(A*R) -> m B) :=
        let f (a:A) := ReaderT $ fun r => f' (a,r) in
        uncurry $ fun (a:A) (r:R) =>
          run_reader_t r $ ff f a
      in
      ReaderT $ fun r => mfix ff' (a,r).
    Global Instance reader_t_MonadFix : MonadFix (reader_t R m) :=
      { mfix := @reader_t_mfix }.
  End MonadFix.

  Section MonadPlus.
    Context {MP:MonadPlus m}.

    Definition reader_t_mzero {A} : reader_t R m A := lift mzero.
    Definition reader_t_mplus {A B}
        (aM:reader_t R m A) (bM:reader_t R m B) : reader_t R m (A+B) :=
      ReaderT $ fun r => un_reader_t aM r <+> un_reader_t bM r.
    Global Instance reader_t_MonadPlus : MonadPlus (reader_t R m) :=
      { mzero := @reader_t_mzero
      ; mplus := @reader_t_mplus
      }.
  End MonadPlus.

  Section MonadError.
    Context {E} {ME:MonadError E m}.

    Definition reader_t_throw {A} : E -> reader_t R m A := lift <.> throw.
    Definition reader_t_catch {A}
        (aM:reader_t R m A) (h:E -> reader_t R m A) : reader_t R m A :=
      ReaderT $ fun r => catch (un_reader_t aM r) $ run_reader_t r <.> h.
    Global Instance reader_t_MonadError : MonadError E (reader_t R m) :=
      { throw := @reader_t_throw
      ; catch := @reader_t_catch
      }.
  End MonadError.
End reader_t.
Require Import FP.Data.Function.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadError.
Require Import FP.Structures.FUnit.
Require Import FP.Structures.MonadFix.
Require Import FP.Structures.MonadReader.
Require Import FP.Structures.MonadState.
Require Import FP.Structures.MonadTrans.

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
  Context {R:Type} {m} {Monad_:Monad m}.

  Definition run_reader_t {A} : R -> reader_t R m A -> m A := flip un_reader_t.

  Section FUnit.
    Definition reader_t_funit {A} : A -> reader_t R m A := ReaderT '.' const '.' funit.
    Global Instance reader_t_FUnit : FUnit (reader_t R m) :=
      { funit := @reader_t_funit }.
  End FUnit.

  Section Monad.
    Definition reader_t_bind {A B} (aMM:reader_t R m A) (f:A -> reader_t R m B) :
        reader_t R m B :=
      ReaderT $ fun r => begin
        a <- un_reader_t aMM r ;;
        un_reader_t (f a) r
      end.
    Global Instance reader_t_MBind : MBind (reader_t R m) :=
      { bind := @reader_t_bind }.
  End Monad.

  Section MReader.
    Definition reader_t_ask : reader_t R m R :=
      ReaderT ret.
    Definition reader_t_local {A} (f:R -> R) (aM: reader_t R m A) : reader_t R m A :=
      ReaderT $ un_reader_t aM '.' f.
    Global Instance reader_t_MReader : MReader R (reader_t R m) :=
      { ask := @reader_t_ask
      ; local := @reader_t_local
      }.
  End MReader.

  Section ReaderT_passthrough.
    Context {R2} {MReader_2:MReader R2 m}.

    Definition reader_t_ask_passthrough : reader_t R m R2 := lift ask.
    Definition reader_t_local_passthrough {A} (f:R2 -> R2) (aM:reader_t R m A) :=
      ReaderT $ local f '.' un_reader_t aM.
    Definition reader_t_MReader_passthrough : MReader R2 (reader_t R m) :=
      {| ask := @reader_t_ask_passthrough
       ; local := @reader_t_local_passthrough
      |}.                                          
  End ReaderT_passthrough.

  Section MState.
    Context {S} {MS:MState S m}.

    Definition reader_t_get : reader_t R m S := lift get.
    Definition reader_t_put : S -> reader_t R m unit := lift '.' put.
    Global Instance reader_t_MState : MState S (reader_t R m) :=
      { get := reader_t_get
      ; put := reader_t_put
      }.
  End MState.

  Section MFix.
    Context {MFix_:MFix m}.

    Definition reader_t_mfix {A B}
        (ff:(A -> reader_t R m B) -> A -> reader_t R m B) (a:A) : reader_t R m B :=
      let ff' (f':(A*R) -> m B) :=
        let f (a:A) := ReaderT $ fun r => f' (a,r) in
        uncurry $ fun (a:A) (r:R) =>
          run_reader_t r $ ff f a
      in
      ReaderT $ fun r => mfix ff' (a,r).
    Global Instance reader_t_MFix : MFix (reader_t R m) :=
      { mfix := @reader_t_mfix }.
  End MFix.

  Section MError.
    Context {E} {MError_:MError E m}.

    Definition reader_t_throw {A} : E -> reader_t R m A := lift '.' throw.
    Definition reader_t_catch {A}
        (aM:reader_t R m A) (h:E -> reader_t R m A) : reader_t R m A :=
      ReaderT $ fun r => catch (un_reader_t aM r) $ run_reader_t r '.' h.
    Global Instance reader_t_MonadError : MError E (reader_t R m) :=
      { throw := @reader_t_throw
      ; catch := @reader_t_catch
      }.
  End MError.
End reader_t.
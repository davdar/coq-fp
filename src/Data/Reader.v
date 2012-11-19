Require Import Data.FunctionPre.

Require Import Structures.Alternative.
Require Import Structures.Monad.
Require Import Structures.MonadError.
Require Import Structures.MonadFix.
Require Import Structures.MonadPlus.
Require Import Structures.MonadReader.
Require Import Structures.MonadTrans.

Import AlternativeNotation.
Import FunctionNotation.
Import MonadNotation.

Inductive reader_t R (m:Type -> Type) A := ReaderT { un_reader_t : R -> m A }.
Arguments ReaderT {R m A} _.
Arguments un_reader_t {R m A} _ _.

Definition run_reader_t {R m A} : R -> reader_t R m A -> m A := flip un_reader_t.

Definition reader_t_ret {R m} {M:Monad m} {A} : A -> reader_t R m A :=
  ReaderT <.> const <.> ret.
Definition reader_t_bind {R m} {M:Monad m} {A B}
    (aMM:reader_t R m A) (f:A -> reader_t R m B) : reader_t R m B :=
  ReaderT $ fun r => begin
    a <- un_reader_t aMM r ;;
    un_reader_t (f a) r
  end.
Instance reader_t_Monad {R m} {M:Monad m} : Monad (reader_t R m) :=
  { ret := @reader_t_ret _ _ _
  ; bind := @reader_t_bind _ _ _
  }.
Definition reader_t_lift {R} {m} {M:Monad m} {A} (aM:m A) : reader_t R m A :=
  ReaderT $ fun r => aM.
Instance reader_t_MonadTrans {R} : MonadTrans (reader_t R) :=
  { lift  := @reader_t_lift _
  }.

Definition reader_t_ask {R m} {M:Monad m} : reader_t R m R :=
  ReaderT $ fun r => ret r.
Definition reader_t_local {R m} {M:Monad m} {A} (f:R -> R) (aM: reader_t R m A) : reader_t R m A :=
  ReaderT $ fun r => un_reader_t aM (f r).
Instance reader_t_MonadReader {R m} {M:Monad m} : MonadReader R (reader_t R m) :=
  { ask := @reader_t_ask _ _ _
  ; local := @reader_t_local _ _ _
  }.

Definition reader_t_ask_passthrough {R1 R2 m} {M:Monad m} {MR:MonadReader R2 m} : reader_t R1 m R2 :=
  lift ask.
Definition reader_t_local_passthrough {R1 R2 m} {M:Monad m} {MR:MonadReader R2 m} {A} (f:R2 -> R2) (aM:reader_t R1 m A) :=
  ReaderT $ local f <.> un_reader_t aM.
Definition reader_t_MonadReader_passthrough {R1 R2 m} {M:Monad m} {MR:MonadReader R2 m} : MonadReader R2 (reader_t R1 m) :=
  {| ask := @reader_t_ask_passthrough _ _ _ _ _
   ; local := @reader_t_local_passthrough _ _ _ _ _
  |}.                                          

Definition reader_t_mfix {R m} {M:Monad m} {MF:MonadFix m} {A B}
    (ff:(A -> reader_t R m B) -> A -> reader_t R m B) (a:A) : reader_t R m B :=
  let ff' (f':(A*R) -> m B) :=
    let f (a:A) := ReaderT $ fun r => f' (a,r) in
    uncurry $ fun (a:A) (r:R) =>
      run_reader_t r $ ff f a
  in
  ReaderT $ fun r => mfix ff' (a,r).
Instance reader_t_MonadFix {R m} {M:Monad m} {MF:MonadFix m} : MonadFix (reader_t R m) :=
  { mfix := @reader_t_mfix _ _ _ _ }.

Definition reader_t_mzero {R m} {M:Monad m} {MP:MonadPlus m} {A} : reader_t R m A :=
  lift mzero.
Definition reader_t_mplus {R m} {M:Monad m} {MP:MonadPlus m} {A B} (aM:reader_t R m A) (bM:reader_t R m B) :=
  ReaderT $ fun r => un_reader_t aM r <+> un_reader_t bM r.
Instance reader_t_MonadPlus {R m} {M:Monad m} {MP:MonadPlus m} : MonadPlus (reader_t R m) :=
  { mzero := @reader_t_mzero _ _ _ _
  ; mplus := @reader_t_mplus _ _ _ _
  }.
      
Definition reader_t_throw {R E m} {M:Monad m} {ME:MonadError E m} {A} : E -> reader_t R m A := lift <.> throw.
Definition reader_t_catch {R E m} {M:Monad m} {ME:MonadError E m} {A}
    (aM:reader_t R m A) (h:E -> reader_t R m A) : reader_t R m A :=
  ReaderT $ fun r => catch (un_reader_t aM r) $ run_reader_t r <.> h.
Instance reader_t_MonadError {R E m} {M:Monad m} {ME:MonadError E m} : MonadError E (reader_t R m) :=
  { throw := @reader_t_throw _ _ _ _ _
  ; catch := @reader_t_catch _ _ _ _ _
  }.
  
  
Require Import FP.Data.Function.
Require Import FP.Data.Identity.
Require Import FP.Data.N.
Require Import FP.Data.Reader.
Require Import FP.Data.Option.
Require Import FP.Structures.Monad.
Require Import FP.Structures.Injection.
Require Import FP.Structures.MonadError.
Require Import FP.Structures.MonadFix.
Require Import FP.Structures.MonadPlus.
Require Import FP.Structures.MonadReader.
Require Import FP.Structures.Functor.
Require Import FP.Structures.MonadState.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.Peano.
Require Import FP.Structures.MonadTrans.

Import FunctionNotation.

Inductive fuel_t m A := FuelT { un_fuel_t : reader_t N (option_t m) A }.
Arguments FuelT {m A} _.
Arguments un_fuel_t {m A} _.

Section MonadTrans.
  Definition fuel_t_lift {m} {M:Monad m} {A} : m A -> fuel_t m A :=
    FuelT '.' lift (m:=option_t m) '.' lift (m:=m).
End MonadTrans. 

Section fuel_t_Monad.
  Context {m} {M:Monad m}.

  Definition mk_fuel_t {A} : (N -> m (option A)) -> fuel_t m A :=
    FuelT '.' ReaderT '.' compose OptionT.
  Definition run_fuel_t {A} (n:N) : fuel_t m A -> m (option A) :=
    run_option_t '.' run_reader_t n '.' un_fuel_t.
  Definition fun_fuel_t {A} : fuel_t m A -> N -> m (option A) :=
    flip run_fuel_t.

  Section MonadFix.
    Definition fuel_t_mfix {A B}
        (ff:(A -> fuel_t m B) -> A -> fuel_t m B) (a:A) : fuel_t m B :=
      mk_fuel_t $ fun n =>
        fold_mfix begin fun (f: N -> A -> m (option B)) (_n:N) (a:A) =>
           run_fuel_t n $ ff begin fun (a:A) =>
             mk_fuel_t $ fun (__n:N) => f _n a
           end a
        end n a.
    Global Instance fuel_t_MonadFix : MonadFix (fuel_t m) :=
      { mfix := @fuel_t_mfix }.
  End MonadFix.

  Global Instance fuel_t_reader_t_FunctorInjection
      : FunctorInjection (fuel_t m) (reader_t N (option_t m)) :=
    { finject := @un_fuel_t _ }.
  Global Instance reader_t_fuel_t_FunctorInjection
      : FunctorInjection (reader_t N (option_t m)) (fuel_t m) :=
    { finject := @FuelT _}.

  Global Instance fuel_t_Monad
      : Monad (fuel_t m) :=
    iso_Monad (reader_t N (option_t m)).
  Global Instance fuel_t_MonadError {E} {ME:MonadError E m}
      : MonadError E (fuel_t m) :=
    iso_MonadError (reader_t N (option_t m)).
  Global Instance fuel_t_MonadState {S} {MS:MonadState S m}
      : MonadState S (fuel_t m) :=
    iso_MonadState (reader_t N (option_t m)).
  Global Instance fuel_t_MonadPlus {MP:MonadPlus m}
      : MonadPlus (fuel_t m) :=
    iso_MonadPlus (nMP:=reader_t_MonadPlus (MP:=option_t_MonadPlus_passthrough))
                  (reader_t N (option_t m)).
  Global Instance fuel_t_MonadReader {R} {MR:MonadReader R m}
      : MonadReader R (fuel_t m) :=
    iso_MonadReader (nMR:=reader_t_MonadReader_passthrough)
                    (reader_t N (option_t m)).
End fuel_t_Monad.

Definition fuel := fuel_t identity.
Definition mk_fuel {A} : (N -> option A) -> fuel A :=
  mk_fuel_t '.' compose Identity.
Definition run_fuel {A} : N -> fuel A -> option A :=
  compose run_identity '.' run_fuel_t.

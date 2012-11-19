Require Import Data.Function.
Require Import Data.Identity.
Require Import Data.N.
Require Import Data.Reader.
Require Import Data.Option.
Require Import Structures.Monad.
Require Import Structures.Injection.
Require Import Structures.MonadError.
Require Import Structures.MonadFix.
Require Import Structures.MonadPlus.
Require Import Structures.MonadReader.
Require Import Structures.Functor.
Require Import Structures.Foldable.

Import FunctionNotation.

Inductive fuel_t m A := FuelT { un_fuel_t : reader_t N (option_t m) A }.
Arguments FuelT {m A} _.
Arguments un_fuel_t {m A} _.

Definition mk_fuel_t {m A} : (N -> m (option A)) -> fuel_t m A := FuelT <.> ReaderT <.> compose OptionT.
Definition run_fuel_t {m A} (n:N) : fuel_t m A -> m (option A) := run_option_t <.> run_reader_t n <.> un_fuel_t.
Definition fun_fuel_t {m A} : fuel_t m A -> N -> m (option A) := flip run_fuel_t.

Definition fuel := fuel_t identity.
Definition mk_fuel {A} : (N -> option A) -> fuel A := mk_fuel_t <.> compose Identity.
Definition run_fuel {A} : N -> fuel A -> option A := compose run_identity <.> run_fuel_t.

Instance fuel_t_reader_t_FunctorInjection {m} : FunctorInjection (fuel_t m) (reader_t N (option_t m)) :=
  { finject := @un_fuel_t _ }.
Instance reader_t_fuel_t_FunctorInjection {m} : FunctorInjection (reader_t N (option_t m)) (fuel_t m) :=
  { finject := @FuelT _}.

Instance fuel_t_Monad {m} {M:Monad m} : Monad (fuel_t m) :=
  iso_Monad (reader_t N (option_t m)).
Instance fuel_t_MonadPlus {m} {M:Monad m} {MP:MonadPlus m} : MonadPlus (fuel_t m) :=
  iso_MonadPlus (reader_t N (option_t m)).
Instance fuel_t_MonadError {E m} {M:Monad m} {ME:MonadError E m} : MonadError E (fuel_t m) :=
  iso_MonadError (reader_t N (option_t m)).
Instance fuel_t_MonadReader {m} {M:Monad m} {R} {MR:MonadReader R m} : MonadReader R (fuel_t m) :=
  iso_MonadReader (reader_t N (option_t m)) (nMR:=reader_t_MonadReader_passthrough).

Definition fuel_t_mfix {m} {M:Monad m} {A B} (ff:(A -> fuel_t m B) -> A -> fuel_t m B) (a:A) : fuel_t m B :=
  mk_fuel_t $ fun n =>
    (fold_mfix $ fun (f:N -> A -> m (option B)) n a =>
       run_fuel_t n $ ff (fun a => mk_fuel_t $ fun n => f n a) a)
    n a.
Instance fuel_t_MonadFix {m} {M:Monad m} : MonadFix (fuel_t m) :=
  { mfix := @fuel_t_mfix _ _ }.
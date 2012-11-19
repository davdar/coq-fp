Require Export Coq.Init.Datatypes.

Require Import Data.FunctionPre.
Require Import Data.Identity.
Require Import Data.StringPre.
Require Import Structures.Functor.
Require Import Structures.Injection.
Require Import Structures.Injection.
Require Import Structures.Monad.
Require Import Structures.MonadError.
Require Import Structures.MonadPlus.
Require Import Structures.MonadReader.
Require Import Structures.MonadTrans.
Require Import Structures.Monoid.

Import FunctionNotation.
Import FunctorNotation.
Import MonadNotation.

(* option *)

Arguments Some {A} _.
Arguments None {A}.

Definition from_option {A} (a:A) (aM:option A) : A :=
  match aM with
  | None => a
  | Some a' => a'
  end.

Section MonadError.
  Context {m E} {mM:Monad m} {mE:MonadError E m} {eI:Injection string E}.

  Definition throw_msg_option {A} (msg:string) (xM:option A) : m A :=
    match xM with
    | None => throw_msg msg
    | Some x => ret x
    end.
End MonadError.

Section MonadPlus.
  Context {m} {M:Monad m} {P:MonadPlus m}.

  Definition zero_option {A} (xM:option A) : m A :=
    match xM with
    | None => mzero
    | Some x => ret x
    end.
End MonadPlus.

Definition monoid_option {m} {M:Monoid m} {A} (f:A -> m) (xM:option A) : m :=
  match xM with
  | None => gunit
  | Some x => f x
  end.

(* option_t *)

Inductive option_t m (A:Type) := OptionT { un_option_t : m (option A) }.
Arguments OptionT {m A} _.
Arguments un_option_t {m A} _.

Definition run_option_t {m A} : option_t m A -> m (option A) := un_option_t.

Section option_t.
  Definition option_t_lift {m} {M:Monad m} {A} : m A -> option_t m A := OptionT <.> fmap Some.
  Global Instance option_t_MonadTrans : MonadTrans option_t :=
    { lift := @option_t_lift }.

  Context {m} {M:Monad m}.

  Definition option_t_ret {A} (a:A) : option_t m A := OptionT $ ret $ Some a.
  Definition option_t_bind {A B} (aMM:option_t m A) (f:A -> option_t m B)
      : option_t m B :=
    OptionT $ begin
      a <- un_option_t aMM ;;
      match a with
      | None => ret None
      | Some a => un_option_t $ f a
      end
    end.

  Global Instance option_t_Monad : Monad (option_t m) :=
    { ret _A := option_t_ret
    ; bind _A _B := option_t_bind
    }.

  Definition option_t_zero {A} : option_t m A := OptionT $ ret None.
  Definition option_t_plus {A} {B} (aMM:option_t m A) (bMM:option_t m B)
      : option_t m (A+B) :=
    OptionT $ begin
      a <- un_option_t aMM ;;
      match a with
      | None => un_option_t $ inr <$> bMM
      | Some x => un_option_t $ inl <$> aMM
      end
    end.

  Global Instance option_t_MonadPlus : MonadPlus (option_t m) :=
    { mzero := @option_t_zero
    ; mplus := @option_t_plus
    }.

  Section MonadError.
    Context {E} {ME:MonadError E m}.
    Definition option_t_throw {A} : E -> option_t m A := lift <.> throw.
    Definition option_t_catch {A} (aMM:option_t m A) : (E -> option_t m A) -> option_t m A :=
      OptionT <.> catch (un_option_t aMM) <.> compose un_option_t.
    Global Instance option_t_MonadError : MonadError E (option_t m) :=
      { throw := @option_t_throw
      ; catch := @option_t_catch
      }.
  End MonadError.

  Section MonadReader.
    Context {R} {MR:MonadReader R m}.
    Definition option_t_ask : option_t m R := lift ask.
    Definition option_t_local {A} (f:R -> R) : option_t m A -> option_t m A :=
      OptionT <.> local f <.> un_option_t.
    Global Instance option_t_MonadReader : MonadReader R (option_t m) :=
      { ask := option_t_ask
      ; local := @option_t_local
      }.
  End MonadReader.
End option_t.

Instance option_option_t_FunctorInjection : FunctorInjection option (option_t identity) :=
  { finject := fun _ => OptionT <.> Identity}.
Instance option_t_option_FunctorInjection : FunctorInjection (option_t identity) option :=
  { finject := fun _ => un_identity <.> un_option_t }.
Instance option_Monad : Monad option := iso_Monad (option_t identity).
Instance option_MonadPlus : MonadPlus option := iso_MonadPlus (option_t identity).

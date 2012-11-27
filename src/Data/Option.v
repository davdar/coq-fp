Require Import FP.Data.FunctionPre.
Require Import FP.Data.Identity.
Require Import FP.Data.StringPre.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadError.
Require Import FP.Structures.MonadPlus.
Require Import FP.Structures.MonadReader.
Require Import FP.Structures.MonadState.
Require Import FP.Structures.MonadTrans.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.Alternative.

Import FunctionNotation.
Import FunctorNotation.
Import MonadNotation.
Import AlternativeNotation.

(* option *)

Arguments Some {A} _.
Arguments None {A}.

Definition from_option {A} (a:A) (aM:option A) : A :=
  match aM with
  | None => a
  | Some a' => a'
  end.

Section throw_msg_option.
  Context {m E} {mM:Monad m} {mE:MonadError E m} {eI:Injection string E}.

  Definition throw_msg_option {A} (msg:string) (xM:option A) : m A :=
    match xM with
    | None => throw_msg msg
    | Some x => ret x
    end.
End throw_msg_option.

Section zero_option.
  Context {m} {M:Monad m} {P:MonadPlus m}.

  Definition zero_option {A} (xM:option A) : m A :=
    match xM with
    | None => mzero
    | Some x => ret x
    end.
End zero_option.

Section monoid_option.
  Context {T} {TM:Monoid T}.
  Definition monoid_option (xM:option T) : T :=
    match xM with
    | None => gunit
    | Some x => x
    end.
End monoid_option.

Section Foldable.
  Context {A:Type}.
  Definition option_cofold {m} {M:Comonad m} {B}
      (f:A -> m B -> B) (b:m B) (aM:option A) : B :=
    match aM with
    | None => coret b
    | Some a => f a b
    end.
  Global Instance option_Foldable : Foldable A (option A) :=
    { cofold := @option_cofold }.
End Foldable.

(* option_t *)

Inductive option_t m (A:Type) := OptionT { un_option_t : m (option A) }.
Arguments OptionT {m A} _.
Arguments un_option_t {m A} _.

Section MonadTrans.
  Definition option_t_lift {m} {M:Monad m} {A} : m A -> option_t m A :=
    OptionT <.> fmap Some.
  Global Instance option_t_MonadTrans : MonadTrans option_t :=
    { lift := @option_t_lift }.
End MonadTrans.

Section option_t_Monad.
  Context {m} {M:Monad m}.

  Definition run_option_t {A} : option_t m A -> m (option A) := un_option_t.

  Section Monad.
    Definition option_t_ret {A} (a:A) : option_t m A := OptionT $ ret $ Some a.
    Definition option_t_bind {A B}
        (aMM:option_t m A) (f:A -> option_t m B) : option_t m B :=
      OptionT $ begin
        a <- un_option_t aMM ;;
        match a with
        | None => ret None
        | Some a => un_option_t $ f a
        end
      end.
    Global Instance option_t_Monad : Monad (option_t m) :=
      { ret := @option_t_ret
      ; bind := @option_t_bind
      }.
  End Monad.

  Section MonadPlus.
    Definition option_t_mzero {A} : option_t m A := OptionT $ ret None.
    Definition option_t_mplus {A} {B}
        (aMM:option_t m A) (bMM:option_t m B) : option_t m (A+B) :=
      OptionT $ begin
        a <- un_option_t aMM ;;
        match a with
        | None => un_option_t $ inr <$> bMM
        | Some x => un_option_t $ inl <$> aMM
        end
      end.

    Global Instance option_t_MonadPlus : MonadPlus (option_t m) :=
      { mzero := @option_t_mzero
      ; mplus := @option_t_mplus
      }.
  End MonadPlus.

  Section MonadError.
    Context {E} {ME:MonadError E m}.

    Definition option_t_throw {A} : E -> option_t m A := lift <.> throw.
    Definition option_t_catch {A}
        (aMM:option_t m A) : (E -> option_t m A) -> option_t m A :=
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

  Section MonadState.
    Context {S} {MS:MonadState S m}.

    Definition option_t_get : option_t m S := lift get.
    Definition option_t_put (s:S) : option_t m unit := lift $ put s.
    Global Instance option_t_MonadState : MonadState S (option_t m) :=
      { get := option_t_get
      ; put := option_t_put
      }.
  End MonadState.
End option_t_Monad.

Instance option_option_t_FunctorInjection
    : FunctorInjection option (option_t identity) :=
  { finject := fun _ => OptionT <.> Identity}.
Instance option_t_option_FunctorInjection
    : FunctorInjection (option_t identity) option :=
  { finject := fun _ => un_identity <.> un_option_t }.
Instance option_Monad : Monad option := iso_Monad (option_t identity).
Instance option_MonadPlus : MonadPlus option := iso_MonadPlus (option_t identity).

Section MonadPlus_passthrough.
  Context {m} {M:Monad m} {MP:MonadPlus m}.

  Definition option_t_mzero_passthrough {A} : option_t m A := OptionT $ mzero.
  Definition option_t_mplus_passthrough {A B}
      (aMM:option_t m A) (bMM:option_t m B) : option_t m (A+B) :=
    OptionT $ begin
      aMbM <- un_option_t aMM <+> un_option_t bMM ;;
      ret $
        match aMbM with
        | inl aM => inl <$> aM
        | inr bM => inr <$> bM
        end
    end.
  Definition option_t_MonadPlus_passthrough : MonadPlus (option_t m) :=
    {| mzero := @option_t_mzero_passthrough
     ; mplus := @option_t_mplus_passthrough
    |}.
End MonadPlus_passthrough.

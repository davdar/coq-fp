Require Import FP.Data.String.
Require Import FP.Data.Function.
Require Import FP.Data.Identity.
Require Import FP.Data.Sum.
Require Import FP.Data.Unit.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Monad.
Require Import FP.Structures.Counit.
Require Import FP.Structures.Injection.
Require Import FP.Structures.FUnit.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadError.
Require Import FP.Structures.Deriving.
Require Import FP.Structures.FUnit.
Require Import FP.Structures.FUnitDeriving.
Require Import FP.Structures.MonadReader.
Require Import FP.Structures.MonadState.
Require Import FP.Structures.MonadReader.
Require Import FP.Structures.MonadDeriving.
Require Import FP.Structures.MonadTrans.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Ord.
Require Import FP.Relations.RelDec.
Require Import FP.Relations.Setoid.
Require Import FP.Relations.Function.

Import AdditiveNotation.
Import EqvNotation.
Import FunctionNotation.
Import FunctorNotation.
Import MonadNotation.
Import ProperNotation.

Arguments Some {A} _.
Arguments None {A}.

Section sum_Bijection.
  Context {A:Type}.

  Definition option_to_sum (aM:option A) : unit + A :=
    match aM with
    | None => inl tt
    | Some a => inr a
    end.
  Global Instance option_to_sum_InjectionResp_eq
      : InjectionRespect (option A) (unit+A) option_to_sum eq eq.
    constructor ; unfold Proper ; simpl in * ; intros ; try congruence.
    destruct x,y ; simpl in * ; congruence.
    Qed.

  Definition sum_to_option (aM:unit+A) : option A :=
    match aM with
    | inl tt => None
    | inr a => Some a
    end.
  Global Instance sum_to_option_InjectionInverse_eq
      : InjectionInverse (unit+A) (option A) sum_to_option option_to_sum eq.
    constructor ; intros.
    destruct x ; [ destruct u | idtac ] ; simpl in * ; auto.
    Qed.
End sum_Bijection.

Module option_DTKS1_Arg <: DerivingTheKitchenSink1_Arg.
  Definition T A := option A.
  Definition U A := (unit:Type)+A.
  Definition to {A} (x:T A) := option_to_sum x.
  Definition from {A} (x:U A) := sum_to_option x.
  Definition InjResp A : InjectionRespect (T A) (U A) to eq eq := _.
  Definition InjInv A : InjectionInverse (U A) (T A) from to eq := _.
End option_DTKS1_Arg.

Module option_DTKS1 := DerivingTheKitchenSink1 option_DTKS1_Arg.
Import option_DTKS1.

Definition from_option {A} (a:A) (aM:option A) : A :=
  match aM with
  | None => a
  | Some a' => a'
  end.

Section throw_msg_option.
  Context {m E} {mM:Monad m} {mE:MError E m} {eI:HasInjection string E}.

  Definition throw_msg_option {A} (msg:string) (xM:option A) : m A :=
    match xM with
    | None => throw_msg msg
    | Some x => ret x
    end.
End throw_msg_option.

(*
Section zero_option.
  Context {m} {M:Monad m} {P:MonadPlus m}.

  Definition zero_option {A} (xM:option A) : m A :=
    match xM with
    | None => mzero
    | Some x => ret x
    end.
End zero_option.
*)

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
    | None => counit b
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
    OptionT '.' bind_fmap Some.
  Global Instance option_t_MonadTrans : MonadTrans option_t :=
    { lift := @option_t_lift }.
End MonadTrans.

Section option_t_Monad.
  Context {m} {M:Monad m}.

  Definition run_option_t {A} : option_t m A -> m (option A) := un_option_t.

  Section Monad.
    Definition option_t_funit {A} (a:A) : option_t m A := OptionT $ ret $ Some a.
    Global Instance option_t_FUnit : FUnit (option_t m) :=
      { funit := @option_t_funit }.

    Definition option_t_bind {A B}
        (aMM:option_t m A) (f:A -> option_t m B) : option_t m B :=
      OptionT $ begin
        a <- un_option_t aMM ;;
        match a with
        | None => ret None
        | Some a => un_option_t $ f a
        end
      end.
    Global Instance option_t_MBind : MBind (option_t m) :=
      { bind := @option_t_bind }.
  End Monad.

  Global Instance option_t_FMap : FMap (option_t m) := Deriving_FMap_MBind.

  Section FPlus.
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
  End FPlus.

  Section MonadError.
    Context {E} {ME:MonadError E m}.

    Definition option_t_throw {A} : E -> option_t m A := lift '.' throw.
    Definition option_t_catch {A}
        (aMM:option_t m A) : (E -> option_t m A) -> option_t m A :=
      OptionT '.' catch (un_option_t aMM) '.' compose un_option_t.
    Global Instance option_t_MonadError : MonadError E (option_t m) :=
      { throw := @option_t_throw
      ; catch := @option_t_catch
      }.
  End MonadError.
*)

  Section MonadReader.
    Context {R} {MR:MReader R m}.

    Definition option_t_ask : option_t m R := lift ask.
    Definition option_t_local {A} (f:R -> R) : option_t m A -> option_t m A :=
      OptionT '.' local f '.' un_option_t.
    Global Instance option_t_MonadReader : MReader R (option_t m) :=
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

Instance option_option_t_HasFunctorInjection
    : HasFunctorInjection option (option_t identity) :=
  { finject := fun _ => OptionT '.' Identity}.
Instance option_t_option_HasFunctorInjection
    : HasFunctorInjection (option_t identity) option :=
  { finject := fun _ => un_identity '.' un_option_t }.

Instance option_FUnit : FUnit option := Deriving_FUnit (option_t identity).
Instance option_MBind : MBind option := Deriving_MBind (option_t identity).
Instance option_FPlus : FPlus option := Deriving_FPlus (option_t identity).

(*
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

*)
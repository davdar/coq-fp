Require Import FP.Data.StringPre.

Require Import FP.Data.Function.
Require Import FP.Data.Identity.
Require Import FP.Data.Sum.
Require Import FP.Data.Unit.
Require Import FP.Structures.Alternative.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadError.
Require Import FP.Structures.MonadPlus.
Require Import FP.Structures.Deriving.
Require Import FP.Structures.MonadReader.
Require Import FP.Structures.MonadState.
Require Import FP.Structures.MonadTrans.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Ord.
Require Import FP.Relations.RelDec.
Require Import FP.Relations.Setoid.
Require Import FP.Relations.Function.

Import AdditiveNotation.
Import MorphismNotation.
Import EqvNotation.
Import AlternativeNotation.
Import FunctionNotation.
Import FunctorNotation.
Import MonadNotation.

Arguments Some {A} _.
Arguments None {A}.

(*
Section Injection.
  Context {A:Type}.
  Global Instance option_Injection_Some : Injection A (option A) Some := {}.
  Global Instance option_InjectionResp_Some_eq
      : InjectionRespect A (option A) Some eq eq.
    constructor ; unfold Proper ; simpl in * ; intros ; congruence. Qed.
End Injection.
*)
  (*
  Global Instance option_InjectionRespect_Some_lt
    : InjectionRespect A (option A) Some lt lt.
  Proof. constructor.
    unfold Proper ; simpl ; intros.
      constructor ; auto.
    unfold Proper ; simpl ; intros.
      inversion H ; auto.
  Qed.
*)
(*
  Global Instance option_InjectionResp_Some_eqv
      : InjectionRespect A (option A) Some eqv eqv.
    constructor ; unfold Proper ; simpl in * ; intros.
    constructor ; auto.
    inversion H ; auto.
    Qed.
*)


Section Bijection_sum.
  Context {A:Type}.

  Definition option_to_sum (aM:option A) : unit + A :=
    match aM with
    | None => inl tt
    | Some a => inr a
    end.
  Global Instance option_InjectionResp_sum_eq
      : InjectionRespect (option A) (unit+A) option_to_sum eq eq.
    constructor ; unfold Proper ; simpl in * ; intros ; try congruence.
    destruct x,y ; simpl in * ; congruence.
    Qed.

  Definition sum_to_option (aM:unit+A) : option A :=
    match aM with
    | inl tt => None
    | inr a => Some a
    end.
  Global Instance sum_InjectionResp_option_eq
     : InjectionRespect (unit+A) (option A) sum_to_option eq eq.
    constructor ; unfold Proper ; simpl in * ; intros ; try congruence.
    destruct x,y ; simpl in *.
      destruct u,u0 ; congruence.
      destruct u ; congruence.
      destruct u ; congruence.
      congruence.
    Qed.

  Global Instance option_InjectionInverse_sum_eq
      : InjectionInverse (option A) (unit+A) option_to_sum sum_to_option eq.
    constructor ; intros.
    destruct x ; simpl in * ; reflexivity.
    Qed.

  Global Instance sum_InjectionInverse_option_eq
      : InjectionInverse (unit+A) (option A) sum_to_option option_to_sum eq.
    constructor ; intros.
    destruct x ; [ destruct u | idtac ] ; simpl in * ; auto.
    Qed.
End Bijection_sum.

Module option_DTKS1_Arg <: DerivingTheKitchenSink1_Arg.
  Definition T := option.
  Definition U := fun A => (unit:Type)+A.
  Definition to := @option_to_sum.
  Definition from := @sum_to_option.
  Definition InjResp : forall A, InjectionRespect (T A) (U A) (to _) eq eq := _.
  Definition InjInv : forall A, InjectionInverse (U A) (T A) (from _) (to _) eq := _.
End option_DTKS1_Arg.

Module option_DTKS1 := DerivingTheKitchenSink1 option_DTKS1_Arg.
Import option_DTKS1.

(*
Section EqDec.
  Context {A} {EqDec_A:EqDec A}.
  Global Instance option_EqDec : EqDec (option A) :=
    { eq_dec := eq_dec `on` option_to_sum }.

  Context {EDC:RelDecCorrect A eq eq_dec}.
  Global Instance option_RelDecCorrect_eq_dec : RelDecCorrect (option A) eq eq_dec :=
    DerivingEqRDC option_to_sum eq_refl.
End EqDec.
Section Eqv.
  Context {A} {Eqv_A:Eqv A}.
  Global Instance option_Eqv : Eqv (option A) :=
    { eqv := eqv `on` option_to_sum }.
  Global Instance option_InjectionResp_sum_eqv
      : InjectionRespect (option A) (unit+A) option_to_sum eqv eqv :=
    DerivingInjResp option_to_sum eqv eqv eq_refl.
  Global Instance sum_InjectionResp_option_eqv
      : InjectionRespect (unit+A) (option A) sum_to_option eqv eqv :=
    DerivingInjResp_inv sum_to_option option_to_sum eqv eqv eq_refl eq.

  Context {A_EqvWF:EqvWF A}.
  Global Instance option_EqvWF : EqvWF (option A) := DerivingEqvWF option_to_sum.
End Eqv.
Section EqvDec.
  Context {A} {EqvDec_A:EqvDec A}.
  Global Instance option_EqvDec : EqvDec (option A) :=
    { eqv_dec := eqv_dec `on` option_to_sum }.

  Context {Eqv_A:Eqv A} {RDC:RelDecCorrect A eqv eqv_dec}.
  Global Instance option_Eqv_RelDecCorrect : RelDecCorrect (option A) eqv eqv_dec :=
    DerivingRelDec option_to_sum eqv eqv_dec eqv eqv_dec eq_refl.
End EqvDec.

Section Ord.
  Context {A} {Ord_A:Ord A}.
  Global Instance option_Ord : Ord (option A) :=
    { lt := lt `on` option_to_sum }.
  Global Instance option_InjectionRespect_sum_lt
      : InjectionRespect (option A) (unit + A) option_to_sum lt lt :=
    DerivingInjResp option_to_sum lt lt eq_refl.

  Global Instance sum_InjectionRespect_option_lt
      : InjectionRespect (unit + A) (option A) sum_to_option lt lt :=
    DerivingInjResp_inv sum_to_option option_to_sum lt lt eq_refl eq.

  Context {Eqv_A:Eqv A} {EqvWF_A:EqvWF A} {OrdWF_A:OrdWF A}.
  Global Instance option_OrdWF : OrdWF (option A) := DerivingOrdWF option_to_sum.
End Ord.
Section OrdDec.
  Context {A} {OrdDec_A:OrdDec A}.
  Global Instance option_OrdDec : OrdDec (option A) :=
    { ord_dec := ord_dec `on` option_to_sum }.

  Context {A_Eqv:Eqv A} {A_Ord:Ord A}.
  Context {A_ODC:OrdDecCorrect A}.
  Global Instance option_OrdDecCorrect : OrdDecCorrect (option A) :=
    DerivingOrdDecCorrect option_to_sum eq_refl.
End OrdDec.

Section Lattice.
  Context {A} {A_Eqv:Eqv A} {A_EqvWF:EqvWF A} {A_Ord:Ord A} {A_OrdWF:OrdWF A}.
  Context {A_Lattice:Lattice A} {A_LatticeWF:LatticeWF A}.
  Global Instance option_Lattice : Lattice (option A) :=
    { lmeet := sum_to_option '..' (lmeet `on` option_to_sum)
    ; ljoin := sum_to_option '..' (ljoin `on` option_to_sum)
    }.
  Global Instance option_InjectionDistribute_meet_eq
      : InjectionDistribute (option A) (unit+A) option_to_sum lmeet lmeet eq :=
    DerivingInjectionDistribute
      option_to_sum sum_to_option lmeet lmeet eq eq eq_refl.
  Global Instance option_InjectionDistribute_meet_eqv
      : InjectionDistribute (option A) (unit+A) option_to_sum lmeet lmeet eqv :=
    DerivingInjectionDistribute_eqv option_to_sum lmeet lmeet eq eqv.

  Global Instance option_InjectionDistribute_join_eq
      : InjectionDistribute (option A) (unit+A) option_to_sum ljoin ljoin eq :=
    DerivingInjectionDistribute
      option_to_sum sum_to_option ljoin ljoin eq eq eq_refl.
  Global Instance option_InjectionDistribute_join_eqv
      : InjectionDistribute (option A) (unit+A) option_to_sum ljoin ljoin eqv :=
    DerivingInjectionDistribute_eqv option_to_sum ljoin ljoin eq eqv.
  Global Instance option_LatticeWF: LatticeWF (option A) :=
    DerivingLatticeWF option_to_sum.
End Lattice.
*)

Definition from_option {A} (a:A) (aM:option A) : A :=
  match aM with
  | None => a
  | Some a' => a'
  end.

Section throw_msg_option.
  Context {m E} {mM:Monad m} {mE:MonadError E m} {eI:HasInjection string E}.

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
    OptionT '.' fmap Some.
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

    Definition option_t_throw {A} : E -> option_t m A := lift '.' throw.
    Definition option_t_catch {A}
        (aMM:option_t m A) : (E -> option_t m A) -> option_t m A :=
      OptionT '.' catch (un_option_t aMM) '.' compose un_option_t.
    Global Instance option_t_MonadError : MonadError E (option_t m) :=
      { throw := @option_t_throw
      ; catch := @option_t_catch
      }.
  End MonadError.

  Section MonadReader.
    Context {R} {MR:MonadReader R m}.

    Definition option_t_ask : option_t m R := lift ask.
    Definition option_t_local {A} (f:R -> R) : option_t m A -> option_t m A :=
      OptionT '.' local f '.' un_option_t.
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
  : FunctorInjection option (option_t identity) (fun _ => OptionT '.' Identity) := {}.
Instance option_t_option_FunctorInjection
  : FunctorInjection (option_t identity) option
                     (fun _ => un_identity '.' un_option_t) := {}.
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

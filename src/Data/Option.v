Require Import FP.Data.StringPre.

Require Import FP.Data.Function.
Require Import FP.Data.Identity.
Require Import FP.Data.Sum.
Require Import FP.Data.Unit.
Require Import FP.Structures.Alternative.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Foldable.
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
Require Import FP.Structures.Ord.
Require Import FP.Relations.RelDec.
Require Import FP.Relations.Setoid.

Import AlternativeNotation.
Import FunctionNotation.
Import FunctorNotation.
Import MonadNotation.

Arguments Some {A} _.
Arguments None {A}.

Instance option_Injection_Some {A}
  : Injection A (option A) Some := {}.
Instance option_InjectionResp_Some_eq {A}
    : InjectionRespect A (option A) Some eq eq.
  constructor ; unfold Proper ; unfold "==>" ; unfold "<==" ; intros.
  rewrite H ; auto.
  injection H ; auto.
  Qed.

Definition option_to_sum {A} (aM:option A) : unit + A :=
  match aM with
  | None => inl tt
  | Some a => inr a
  end.

Definition sum_to_option {A} (aM:unit+A) : option A :=
  match aM with
  | inl tt => None
  | inr a => Some a
  end.

Instance option_Injection_sum {A}
  : Injection (option A) (unit + A) option_to_sum := {}.
Instance sum_Injection_option {A}
  : Injection (unit + A) (option A) sum_to_option := {}.

Instance option_InjectionResp_sum_eq {A}
    : InjectionRespect (option A) (unit+A) option_to_sum eq eq.
  constructor ; unfold Proper ; unfold "==>" ; unfold "<==" ; intros.
  rewrite H ; auto.
  destruct x,y ; simpl in * ; try congruence.
  Qed.
Instance sum_InjectionResp_option_eq {A}
   : InjectionRespect (unit+A) (option A) sum_to_option eq eq.
  constructor ; unfold Proper ; unfold "==>" ; unfold "<==" ; intros.
  rewrite H ; auto.
  destruct x,y ; simpl in * ; try congruence.
  destruct u,u0 ; try congruence.
  destruct u ; try congruence.
  destruct u ; try congruence.
  Qed.


Section EqDec.
  Context {A} {EqDec_A:EqDec A}.
  Global Instance option_EqDec : EqDec (option A) :=
    { eq_dec := eq_dec `on` option_to_sum }.

  Context {EDC:RelDecCorrect (T:=A) eq_dec eq}.

  Global Instance option_RelDecCorrect_eq_dec : RelDecCorrect (T:=option A) eq_dec eq.
    constructor ; intros ; constructor ; intros ; simpl in * ;
      unfold on in * ; simpl in *.
    apply (proj1 rel_dec_correct) in H.
      apply inject_resp_beta ; auto.
    apply rel_dec_correct.
      apply inject_resp_eta ; auto.
    Qed.
End EqDec.
Section Eqv.
  Context {A} {Eqv_A:Eqv A}.
  Global Instance option_Eqv : Eqv (option A) :=
    { eqv := eqv `on` option_to_sum }.

  Global Instance option_InjectionResp_sum_eqv
      : InjectionRespect (option A) (unit+A) option_to_sum eqv eqv.
    constructor ; unfold Proper ; unfold "==>" ; unfold "<==" ; intros.
    unfold eqv in H ; simpl in H ; unfold on in H ; auto.
    unfold eqv ; simpl ; unfold on ; auto.
    Qed.
  Global Instance sum_InjectionResp_option_eqv
      : InjectionRespect (unit+A) (option A) sum_to_option eqv eqv.
    constructor ; unfold Proper ; unfold "==>" ; unfold "<==" ; intros.
    unfold eqv ; simpl ; unfold on ; auto.
    pose (bijection_rel_from_to(mto := sum_to_option)).
    rewrite <- (bijection_rel_from_to).
    apply inject_resp_eta.
    unfold eqv ; simpl ; unfold on ; auto.
           
    apply inject_resp_eta.
    admit.
    unfold eqv in H ; simpl in H ; unfold on in H.
    unfold option_to_sum ; unfold sum_to_option ; simpl.
    unfold Proper in p. unfold "<==" in p.
    rewrite <- p.
    unfold eqv in H ; simpl in H ; unfold on in H ; auto.
    Qed.

  Context {A_EqvWF:EqvWF A}.

  Global Instance option_EqvWF : EqvWF (option A).
    constructor.
    eapply inj_eqv_Equivalence.
    constructor ; constructor ;
      pose (sum_EqvWF (A:=unit) (B:=A)) ;
      destruct e.
    unfold Reflexive ; intros.
      unfold eqv in * ; simpl in * ; unfold on in * ; apply reflexivity.
    unfold Symmetric ; intros.
      unfold eqv in * ; simpl in * ; unfold on in * ; apply symmetry ; auto.
    unfold Transitive ; intros.
      unfold eqv in * ; simpl in * ; unfold on in * ; eapply transitivity ; eauto.
    Qed.
End Eqv.
Section EqvDec.
  Context {A} {EqvDec_A:EqvDec A}.
  Global Instance option_EqvDec : EqvDec (option A) :=
    { eqv_dec := eqv_dec `on` option_to_sum }.
End EqvDec.
Section Ord.
  Context {A} {Ord_A:Ord A}.
  Global Instance option_Ord : Ord (option A) :=
    { lt := lt `on` option_to_sum }.
End Ord.
Section OrdDec.
  Context {A} {OrdDec_A:OrdDec A}.
  Global Instance option_OrdDec : OrdDec (option A) :=
    { ord_dec := ord_dec `on` option_to_sum }.
End OrdDec.

Definition from_option {A} (a:A) (aM:option A) : A :=
  match aM with
  | None => a
  | Some a' => a'
  end.

Section throw_msg_option.
  Context {m E inj} {mM:Monad m} {mE:MonadError E m} {eI:Injection string E inj}.

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
    : FunctorInjection option (option_t identity) :=
  { finject := fun _ => OptionT '.' Identity}.
Instance option_t_option_FunctorInjection
    : FunctorInjection (option_t identity) option :=
  { finject := fun _ => un_identity '.' un_option_t }.
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

Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Deriving.
Require Import FP.Data.Option.
Require Import FP.Structures.Ord.
Require Import FP.Data.Function.
Require Import FP.Data.Sum.
Require Import FP.Data.SumStructures.
Require Import FP.Data.SumRelations.
Require Import FP.Data.Unit.
Require Import FP.Relations.Setoid.

Import AdditiveNotation.
Import FunctionNotation.
Import LatticeNotation.
Import OrdNotation.
Import ProperNotation.

Definition ext_bot := option.

Inductive ext_top A := ExtTop { un_ext_top : option A }.
Global Arguments ExtTop {A} _.
Global Arguments un_ext_top {A} _.

Section ext_top_Bijection.
  Context {A:Type}.

  Definition ext_top_to_sum (et:ext_top A) : A + unit :=
    match un_ext_top et with
    | None => inr tt
    | Some a => inl a
    end.
  Global Instance ext_top_sum_InjectionRespect_eq
      : InjectionRespect (ext_top A) (A+unit) ext_top_to_sum eq eq.
  Proof. constructor ; unfold Proper ; simpl in * ; intros.
    congruence.
    destruct x as [x], y as [y] ; destruct x,y ; simpl in * ;
    unfold ext_top_to_sum ; simpl ; congruence.
  Qed.

  Definition sum_to_ext_top (et:A+unit) : ext_top A :=
    ExtTop $
      match et with
      | inr tt => None
      | inl a => Some a
      end.
  Global Instance sum_ext_top_InjectionInverse_eq
      : InjectionInverse (A+unit) (ext_top A) sum_to_ext_top ext_top_to_sum eq.
  Proof. constructor ; intros ;
      destruct x ; [ idtac | destruct u ] ; simpl ; unfold ext_top_to_sum ; simpl ;
      auto.
  Qed.
End ext_top_Bijection.

Module ext_top_DTKS1_Arg <: DerivingTheKitchenSink1_Arg.
  Definition T A := ext_top A.
  Definition U A := A+(unit:Type).
  Definition to {A} (x:T A) := ext_top_to_sum x.
  Definition from {A} (x:U A) := sum_to_ext_top x.
  Definition InjResp A : InjectionRespect (T A) (U A) to eq eq := _.
  Definition InjInv A : InjectionInverse (U A) (T A) from to eq := _.
End ext_top_DTKS1_Arg.

Module ext_top_DTKS1 := DerivingTheKitchenSink1 ext_top_DTKS1_Arg.
Import ext_top_DTKS1.

Inductive ext_top_bot A := ExtTopBot { un_ext_top_bot : option (option A) }.
Global Arguments ExtTopBot {A} _.
Global Arguments un_ext_top_bot {A} _.

Section ext_top_bot_Bijection.
  Context {A:Type}.

  Definition ext_top_bot_to_sum (e:ext_top_bot A) : unit + A + unit :=
    match un_ext_top_bot e with
    | None => inr tt
    | Some None => inl (inl tt)
    | Some (Some a) => inl (inr a)
    end.
  Global Instance ext_top_bot_InjectionRespect_eq
      : InjectionRespect (ext_top_bot A) (unit+A+unit) ext_top_bot_to_sum eq eq.
  Proof. constructor ; unfold Proper ; simpl ; intros.
    congruence.
    unfold "<==" ; intros.
    destruct x as [x], y as [y] ;
      destruct x as [ x |], y as [y |] ;
      [ destruct x,y | destruct x | destruct y |] ;
      simpl in * ;
      unfold ext_top_bot_to_sum in * ; simpl in * ; congruence.
  Qed.

  Definition sum_to_ext_top_bot (e:unit+A+unit) : ext_top_bot A :=
    ExtTopBot $
      match e with
      | inr tt => None
      | inl (inl tt) => Some None
      | inl (inr a) => Some (Some a)
      end.
  Global Instance sum_ext_top_bot_InjectionInverse_eq
      : InjectionInverse (unit+A+unit) (ext_top_bot A)
                         sum_to_ext_top_bot ext_top_bot_to_sum eq.
  Proof. constructor ; intros.
    destruct x as [x | u] ; [destruct x as [u | x] ; [destruct u |] | destruct u] ;
      unfold ext_top_bot_to_sum ; simpl in * ; congruence.
  Qed.
End ext_top_bot_Bijection.

Module ext_top_bot_DTKS1_Arg <: DerivingTheKitchenSink1_Arg.
  Definition T A := ext_top_bot A.
  Definition U A := (unit:Type)+A+unit.
  Definition to {A} (x:T A) := ext_top_bot_to_sum x.
  Definition from {A} (x:U A) := sum_to_ext_top_bot x.
  Definition InjResp A : InjectionRespect (T A) (U A) to eq eq := _.
  Definition InjInv A : InjectionInverse (U A) (T A) from to eq := _.
End ext_top_bot_DTKS1_Arg.

Module ext_top_bot_DTKS1 := DerivingTheKitchenSink1 ext_top_bot_DTKS1_Arg.
Import ext_top_bot_DTKS1.

Section Injection.
  Context {A:Type} {E:Eqv A} {O:Ord A} {BL:BoundedLattice A}.

  Global Instance ext_top_bot_HasInjection : HasInjection A (ext_top_bot A) :=
    { inject := ExtTopBot '.' Some '.' Some }.
  Global Instance ext_top_bot_InjectionRespect_inject_eq
      : InjectionRespect A (ext_top_bot A) inject eq eq.
  Proof. constructor ; unfold Proper ; simpl ; intros.
    congruence.
    unfold "<==" ; intros ;
      unfold inject in H ; simpl in H ; congruence.
  Qed.
  Global Instance ext_top_bot_InjectionRespect_inject_eqv
      : InjectionRespect A (ext_top_bot A) inject eqv eqv.
  Proof. constructor ; unfold Proper,"==>","<==" ; simpl ; intros.
    apply InjectionRespect_beta ; simpl.
      unfold ext_top_bot_to_sum, inject ; simpl.
      repeat apply InjectionRespect_eta ; auto.
      auto.
    apply InjectionRespect_eta in H ; simpl in H.
      unfold ext_top_bot_to_sum, inject in H ; simpl in H.
      repeat apply InjectionRespect_beta in H ; auto.
  Qed.
  Global Instance ext_top_bot_inject_InjectionRespect_lt
      : InjectionRespect A (ext_top_bot A) inject lt lt.
  Proof.
    constructor ; unfold Proper,"==>","<==" ; simpl ; intros.
    apply InjectionRespect_beta ; simpl.
      unfold ext_top_bot_to_sum, inject ; simpl.
      repeat apply InjectionRespect_eta ; auto.
      auto.
    apply InjectionRespect_eta in H ; simpl in H.
      unfold ext_top_bot_to_sum, inject in H ; simpl in H.
      repeat apply InjectionRespect_beta in H ; auto.
    Qed.

  Lemma ext_top_bot_inject_ineq :
    forall (a:A), lbot < (inject (U:=ext_top_bot A)) a < ltop.
  Proof. intros ; constructor.
    apply InjectionRespect_beta ; simpl.
      compute.
      repeat constructor.
    apply InjectionRespect_beta ; simpl.
      compute.
      repeat constructor.
  Qed.
End Injection.
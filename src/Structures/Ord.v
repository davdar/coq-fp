Require Import FP.Data.BoolPre.
Require Import FP.Data.Function.
Require Import FP.Structures.Injection.
Require Import FP.Relations.Function.
Require Import FP.Structures.Eqv.
Require Import FP.Relations.Setoid.
Require Import FP.Relations.RelDec.

Import BoolNotation.
Import FunctionNotation.
Import MorphismNotation.

Class Ord T := { lt : T -> T -> Prop}.
Arguments lt {T Ord} _ _ : simpl never.

Require Import Coq.Classes.Morphisms.
Class OrdWF T {T_Eqv:Eqv T} {T_Ord:Ord T} :=
  { lt_Irreflexive :> Irreflexive lt
  ; lt_Transitive :> Transitive lt
  ; lt_resp_eqv :> Proper (eqv ==> eqv ==> impl) lt
  }.

Class OrdDec T := { ord_dec : T -> T -> comparison}.

Class OrdDecCorrect T {T_Eqv:Eqv T} {T_Ord:Ord T} {T_OrdDec:OrdDec T} :=
  { ord_rel_correct_eqv : forall {x:T} {y:T}, eqv x y -> ord_dec x y = Eq
  ; ord_rel_correct_lt : forall {x:T} {y:T}, lt x y -> ord_dec x y = Lt
  ; ord_rel_correct_gt : forall {x:T} {y:T}, lt y x -> ord_dec x y = Gt
  ; ord_dec_correct_eqv : forall {x:T} {y:T}, ord_dec x y = Eq -> eqv x y
  ; ord_dec_correct_lt : forall {x:T} {y:T}, ord_dec x y = Lt -> lt x y
  ; ord_dec_correct_gt : forall {x:T} {y:T}, ord_dec x y = Gt -> lt y x
  }.

Section Ord.
  Context {T} {T_Eqv:Eqv T} {T_EqvWF:EqvWF T} {T_Ord:Ord T} {T_OrdWF:OrdWF T}.

  Global Instance lt_Asymmetric : Asymmetric lt.
    unfold Asymmetric ; intros.
    apply (lt_Irreflexive x).
    transitivity y ; auto.
    Qed.

  Definition lte x y := lt x y \/ eqv x y.

  Global Instance lte_Reflexive : Reflexive lte.
    unfold Reflexive ; intros.
    right ; reflexivity.
    Qed.
  Global Instance lte_Transitive : Transitive lte.
    unfold Transitive ; intros * * * e1 e2.
    destruct e1 as [e1 | e1], e2 as [e2 | e2].
    left ; transitivity y ; auto.
    left ; rewrite <- e2 ; auto.
    left ; rewrite -> e1 ; auto.
    right ; transitivity y ; auto.
    Qed.
  Global Instance lte_Antisymmetric : Antisymmetric T eqv lte.
    unfold Antisymmetric ; intros * * e1 e2.
    destruct e1 as [e1 | e1], e2 as [e2 | e2] ; auto ; exfalso.
    apply (lt_Asymmetric x y) ; auto.
    rewrite e2 in e1 ; apply (lt_Irreflexive x) ; auto.
    Qed.

  Global Instance lte_resp_eqv : Proper (eqv ==> eqv ==> iff) lte.
    unfold Proper, "==>" ; intros x x' x_eqv y y' y_eqv ;
    constructor ; intros xy_lte ; destruct xy_lte.
    left ; rewrite <- x_eqv ; rewrite <- y_eqv ; auto.
    right ; rewrite <- x_eqv ; rewrite <- y_eqv ; auto.
    left ; rewrite x_eqv ; rewrite y_eqv ; auto.
    right ; rewrite x_eqv ; rewrite y_eqv ; auto.
    Qed.
End Ord.

Section Injection.
  Context {A} {A_Eqv:Eqv A} {A_Ord:Ord A}.
  Context {B} {B_Eqv:Eqv B} {B_Ord:Ord B}.
  Context {inj:A->B}.
  Context {InjResp_eqv:InjectionRespect A B inj eqv eqv}.
  Context {InjResp_lt:InjectionRespect A B inj lt lt}.

  Global Instance inject_resp_lte : InjectionRespect A B inj lte lte.
    constructor ; unfold Proper ; simpl ; intros x y xy_lte ;
    destruct xy_lte.
      left ; eapply InjectionRespect_eta ; auto.
      right ; eapply InjectionRespect_eta ; auto.
      left ; eapply InjectionRespect_beta ; auto.
      right ; eapply InjectionRespect_beta ; auto.
    Qed.
End Injection.

Section OrdDec.
  Context {T} {T_OrdDec:OrdDec T}.

  Definition lt_dec x y :=
    match ord_dec x y with Lt => true  | Eq => false | Gt => false end.
  Definition lte_dec x y :=
    match ord_dec x y with Lt => true  | Eq => true  | Gt => false end.

  Context {T_Eqv:Eqv T} {T_Ord:Ord T}.
  Context {T_ODC:OrdDecCorrect T}.

  Global Instance lt_RelDecCorrect : RelDecCorrect T lt lt_dec.
  Proof. constructor ; intros x y H ; unfold lt_dec in * ;
      remember (ord_dec x y) as o ; destruct o ; try congruence.
    pose (ord_rel_correct_lt H) ; congruence.
    pose (ord_rel_correct_lt H) ; congruence.
    apply ord_dec_correct_lt ; auto.
  Qed.

  Global Instance lte_RelDecCorrect : RelDecCorrect T lte lte_dec.
  Proof. constructor ; intros x y H ; unfold lte_dec in * ;
      remember (ord_dec x y) as o ; destruct o ; try congruence.
    destruct H as [ ltH | eqvH ].
      pose (ord_rel_correct_lt ltH) ; congruence.
      pose (ord_rel_correct_eqv eqvH) ; congruence.
    right ; apply ord_dec_correct_eqv ; auto. 
    left ; apply ord_dec_correct_lt ; auto.
  Qed.

  Definition ord_dec_p (x:T) (y:T) : {lt x y}+{eqv x y}+{lt y x}.
  Proof.
    remember (ord_dec x y) as o ; destruct o.
    left ; right ; apply ord_dec_correct_eqv ; auto.
    left ; left ; apply ord_dec_correct_lt ; auto.
    right ; apply ord_dec_correct_gt ; auto.
    Qed.
  Definition lt_dec_p (x:T) (y:T) : {lt x y}+{~lt x y}.
  Proof.
    remember (lt_dec x y) as o ; destruct o.
    left ; apply dec_correct ; auto.
    right ; apply neg_dec_correct ; auto.
  Qed.
  Definition lte_dec_p (x:T) (y:T) : {lte x y}+{~lte x y}.
  Proof.
    remember (lte_dec x y) as o ; destruct o.
    left ; apply dec_correct ; auto.
    right ; apply neg_dec_correct ; auto.
  Qed.
End OrdDec.

Module OrdNotation.
  Notation "x < y"         := (lt x y)
    (at level 70, no associativity).
  Notation "x < y < z"     := (lt x y /\ lt y z)
    (at level 70, y at next level, no associativity).
  Notation "x > y"         := (lt y x)
    (at level 70, no associativity, only parsing).
  Notation "x > y > z"     := (lt z y /\ lt y x)
    (at level 70, y at next level, no associativity, only parsing).

  Notation "x <= y"        := (lte x y)
    (at level 70, no associativity).
  Notation "x <= y <= z"   := (lte x y /\ lte y z)
    (at level 70, y at next level, no associativity).
  Notation "x >= y"        := (lte y x)
    (at level 70, no associativity, only parsing).
  Notation "x >= y >= z"   := (lte z y /\ lte y x)
    (at level 70, y at next level, no associativity, only parsing).

  Notation "x <! y"        := (lt_dec x y)
    (at level 35, no associativity).
  Notation "x <! y <! z"   := (lt_dec x y && lt_dec y z)
    (at level 35, y at next level, no associativity).
  Notation "x >! y"        := (lt_dec y x)
    (at level 35, no associativity, only parsing).
  Notation "x >! y >! z"   := (lt_dec z y && lt_dec y x)
    (at level 35, y at next level, no associativity).

  Notation "x <=! y"       := (lte_dec x y)
    (at level 35, no associativity).
  Notation "x <=! y <=! z" := (lte_dec x y && lte_dec y z)
    (at level 35, y at next level, no associativity).
  Notation "x >=! y"       := (lte_dec y x)
    (at level 35, no associativity, only parsing).
  Notation "x >=! y >=! z" := (lte_dec z y && lte_dec y x)
    (at level 35, y at next level, no associativity, only parsing).

  Notation "x <? y"        := (lt_dec_p x y)
    (at level 35, no associativity).
  Notation "x <? y <? z"   := (lt_dec_p x y /\ lt_dec_p y z)
    (at level 35, y at next level, no associativity).
  Notation "x >? y"        := (lt_dec_p y x)
    (at level 35, no associativity, only parsing).
  Notation "x >? y >? z"   := (lt_dec_p z y /\ lt_dec_p y x)
    (at level 35, y at next level, no associativity, only parsing).

  Notation "x <=? y"       := (lte_dec_p x y)
    (at level 35, no associativity).
  Notation "x <=? y <=? z" := (lte_dec_p x y /\ lte_dec_p y z)
    (at level 35, y at next level, no associativity).
  Notation "x >=? y"       := (lte_dec_p y x)
    (at level 35, no associativity, only parsing).
  Notation "x >=? y >=? z" := (lte_dec_p z y /\ lte_dec_p y x)
    (at level 35, y at next level, no associativity, only parsing).

  Notation "x <=>! y"      := (ord_dec x y)
    (at level 35, no associativity).

  Notation "x <=>? y"      := (ord_dec_p x y)
    (at level 35, no associativity).
End OrdNotation.
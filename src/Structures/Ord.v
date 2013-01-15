Require Import FP.Data.BoolPre.
Require Import FP.Data.Function.
Require Import FP.Structures.RelationClasses.
Require Import FP.Structures.Injection.
Require Import FP.Relations.Function.
Require Import FP.Structures.Eqv.
Require Import FP.Relations.Setoid.
Require Import FP.Relations.RelDec.
Open Scope signature_scope.

Import BoolNotation.
Import RespectNotation.
Import FunctionNotation.

Class Ord T :=
  { ord_Eqv :> Eqv T
  ; lt : T -> T -> Prop
  }.
Class OrdWF T {O:Ord T} :=
  { ord_wf_EqvWF :> EqvWF T
  ; lt_Irreflexive :> Irreflexive lt
  ; lt_Transitive :> Transitive lt
  ; lt_resp_eqv :> Proper (eqv ==> eqv ==> iff) lt
  }.

Class OrdDec T :=
  { ord_dec_EqvDec :> EqvDec T
  ; ord_dec : T -> T -> comparison
  }.

Class OrdDecCorrect T {O:Ord T} {OD:OrdDec T} :=
  { ord_dec_correct_eq : forall (x:T) (y:T),
      ord_dec x y = Eq <-> eqv x y
  ; ord_dec_correct_lt : forall (x:T) (y:T),
      ord_dec x y = Lt <-> lt x y
  ; ord_dec_correct_gt : forall (x:T) (y:T),
      ord_dec x y = Gt <-> lt y x
  }.

Section Ord.
  Context {T} {O:Ord T} {WF:OrdWF T}.

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
    unfold Proper ; unfold "==>" ; intros ; constructor ; intros lteH ;
      destruct lteH.
    left ; rewrite <- H ; rewrite <- H0 ; auto.
    right ; rewrite <- H ; rewrite <- H0 ; auto.
    left ; rewrite H ; rewrite H0 ; auto.
    right ; rewrite H ; rewrite H0 ; auto.
    Qed.
End Ord.

Section Injection.
  Context {A B mor} {AO:Ord A} {BO:Ord B} {Inj:Injection A B mor}
          {InjResp_eqv:InjectionRespect A B mor eqv eqv}
          {InjResp_lt:InjectionRespect A B mor lt lt}.

  Global Instance inject_resp_lte : InjectionRespect A B mor lte lte.
    constructor ; unfold Proper ; unfold "==>"%signature ; unfold "<==" ; intros.
    destruct H.
      left ; eapply inject_resp_eta ; auto.
      right ; eapply inject_resp_eta ; auto.
    destruct H.
      left ; eapply inject_resp_beta ; auto.
      right ; eapply inject_resp_beta ; auto.
    Qed.
End Injection.

Section OrdDec.
  Context {T} {tOD:OrdDec T}.

  Definition lt_dec x y :=
    match ord_dec x y with Lt => true  | Eq => false | Gt => false end.
  Definition lte_dec x y :=
    match ord_dec x y with Lt => true  | Eq => true  | Gt => false end.

  Context {O:Ord T}.
  Context {ORDC:OrdDecCorrect T}.

  Global Instance lt_RelDecCorrect : RelDecCorrect (T:=T) lt_dec lt.
    constructor ; intros ; constructor ; intros.
    unfold lt_dec in H.
      remember (ord_dec x y) as o ; destruct o ; try congruence.
      apply ord_dec_correct_lt ; auto.
    unfold lt_dec.
      remember (ord_dec x y) as o ; destruct o ; try congruence ; exfalso.
      pose (proj2 (ord_dec_correct_lt x y) H) ; congruence.
      pose (proj2 (ord_dec_correct_lt x y) H) ; congruence.
    Qed.

  Global Instance lte_RelDecCorrect : RelDecCorrect (T:=T) lte_dec lte.
    constructor ; intros ; constructor ; intros.
    unfold lte_dec in H.
      remember (ord_dec x y) as o ; destruct o ; try congruence.
        right ; apply ord_dec_correct_eq ; auto.
        left ; apply ord_dec_correct_lt ; auto.
    unfold lte_dec.
      remember (ord_dec x y) as o ; destruct o ; try congruence.
      destruct H ; exfalso.
        pose (proj2 (ord_dec_correct_lt x y) H) ; congruence.
        pose (proj2 (ord_dec_correct_eq x y) H) ; congruence.
    Qed.

  Definition ord_dec_p (x:T) (y:T) : {lt x y}+{eqv x y}+{lt y x}.
    remember (ord_dec x y) as o ; destruct o.
    left ; right ; apply (ord_dec_correct_eq x y) ; auto.
    left ; left ; apply (ord_dec_correct_lt x y) ; auto.
    right ; apply (ord_dec_correct_gt x y) ; auto.
    Qed.
  Definition lt_dec_p (x:T) (y:T) : {lt x y}+{~lt x y}.
    remember (lt_dec x y) as o ; destruct o.
    left ; apply rel_dec_correct ; auto.
    right ; apply neg_rel_dec_correct ; auto.
    Qed.
  Definition lte_dec_p (x:T) (y:T) : {lte x y}+{~lte x y}.
    remember (lte_dec x y) as o ; destruct o.
    left ; apply rel_dec_correct ; auto.
    right ; apply neg_rel_dec_correct ; auto.
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
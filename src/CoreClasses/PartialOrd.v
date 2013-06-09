Require Import FP.CoreClasses.Eqv.
Require Import FP.CoreClasses.Setoid.
Require Import FP.CoreClasses.PreOrd.
Require Import FP.CoreClasses.Injection.
Require Import FP.CoreData.Function.
Require Import FP.CoreData.Bool.

Import BoolNotation.

Class PartialOrd T `{! Lte T ,! Eqv T ,! ER_WF T } :=
  { PartialOrd_PreOrd :> PreOrd T
  ; PartialOrd_Antisymmetry :> Antisymmetric T eqv lte
  ; PartialOrd_respect_eqv :> Proper (eqv ==> eqv ==> impl) lte
  }.
Class PartialOrdDec T :=
  { pord_dec : T -> T -> option comparison }.

Section lt_un.
  Context {T} `{! Eqv T ,! Lte T ,! ER_WF T ,! PartialOrd T }.

  Global Instance lt_respect_eqv : Proper (eqv ==> eqv ==> impl) lt.
  Proof.
    unfold Proper,"==>",impl,Basics.impl ; intros.
    destruct H1 ; constructor.
    - rewrite <- H ; rewrite <- H0 ; auto.
    - unfold "~" in * ; intros ; apply H2.
      rewrite H ; rewrite H0 ; auto.
  Qed.

  Global Instance un_respect_eqv : Proper (eqv ==> eqv ==> impl) un.
  Proof.
    unfold Proper,"==>",impl,Basics.impl ; intros.
    destruct H1 ; constructor ; unfold "~" in * ; intros.
    - apply H1.
      rewrite H0 ; rewrite H ; auto.
    - apply H2.
      rewrite H0 ; rewrite H ; auto.
  Qed.
End lt_un.

Class PartialOrd_RDC T `{! Lte T ,! Eqv T ,! ER_WF T ,! PartialOrd T ,! PartialOrdDec T } :=
  { pord_rel_correct_eqv : forall x y, eqv x y -> pord_dec x y = Some Eq
  ; pord_rel_correct_lt : forall x y, lt x y -> pord_dec x y = Some Lt
  ; pord_rel_correct_gt : forall x y, lt y x -> pord_dec x y = Some Gt
  ; pord_rel_correct_un : forall x y, un x y -> pord_dec x y = None
  ; pord_dec_correct_eqv : forall x y, pord_dec x y = Some Eq -> eqv x y
  ; pord_dec_correct_lt : forall x y, pord_dec x y = Some Lt -> lt x y
  ; pord_dec_correct_gt : forall x y, pord_dec x y = Some Gt -> lt y x
  ; pord_dec_correct_un : forall x y, pord_dec x y = None -> un x y
  }.

Section lt_un_IR.
  Context {T U} inj
    `{! Lte T ,! Eqv T ,! ER_WF T ,! PartialOrd T
     ,! Lte U ,! Eqv U ,! ER_WF U ,! PartialOrd U
     ,! InjectionRespect T U inj lte lte
     }.

  Global Instance IR_inj_lt : InjectionRespect T U inj lt lt.
  Proof.
    constructor.
    - unfold Proper,"==>" ; intros.
      destruct H ; constructor.
      + apply InjectionRespect_eta in H ; auto.
      + unfold "~" in * ; intros ; apply H0.
        apply InjectionRespect_beta ; auto.
    - unfold Proper,inverse_respectful ; intros.
      destruct H ; constructor.
      + apply InjectionRespect_beta in H ; auto.
      + unfold "~" in * ; intros ; apply H0.
        apply InjectionRespect_eta ; auto.
  Qed.

  Global Instance IR_inj_un : InjectionRespect T U inj un un.
  Proof.
    constructor.
    - unfold Proper,"==>" ; intros.
      destruct H ; constructor ; unfold "~" in * ; intros.
      + apply H.
        apply InjectionRespect_beta ; auto.
      + apply H0.
        apply InjectionRespect_beta ; auto.
    - unfold Proper,inverse_respectful ; intros.
      destruct H ; constructor ; unfold "~" in * ; intros.
      + apply H.
        apply InjectionRespect_eta ; auto.
      + apply H0.
        apply InjectionRespect_eta ; auto.
  Qed.
      
End lt_un_IR.

Section lt_un_dec.
  Context {T}
    `{! Lte T ,! Lte T ,! LteDec T ,! Eqv T ,! ER_WF T
     ,! PartialOrd T ,! PartialOrdDec T ,! PartialOrd_RDC T
     }.

  Definition pord_dec_p (x:T) (y:T) : {eqv x y}+{lt x y}+{lt y x}+{un x y}.
  Proof.
    remember (pord_dec x y) as o ; destruct o.
    - destruct c.
      + left ; left ; left ; apply pord_dec_correct_eqv ; auto.
      + left ; left ; right ; apply pord_dec_correct_lt ; auto.
      + left ; right ; apply pord_dec_correct_gt ; auto.
    - right ; apply pord_dec_correct_un ; auto.
  Qed.

  Definition lte_from_pord_dec x y :=
    match pord_dec x y with
    | Some Lt => true
    | Some Eq => true
    | _ => false
    end.

  Definition pord_dec_from_lte x y :=
    match lte_dec x y, lte_dec y x with
    | true, true => Some Gt
    | true, false => Some Lt
    | false, true => Some Gt
    | false, false => None
    end.

  Definition eqv_impl_lte : forall {x y}, eqv x y -> lte x y.
  Proof.
    intros.
    rewrite H ; reflexivity.
  Qed.

  Definition lt_dec x y :=
    match pord_dec x y with Some Lt => true | _ => false end.
  Definition lt_dec_p (x:T) (y:T) : {lt x y}+{~lt x y}.
  Proof.
    pose (pord_dec_p x y) ;
    repeat match goal with
    | [ H : sumbool _ _ |- _ ] => destruct H
    | [ H : sumor _ _ |- _ ] => destruct H
    end.
    - right ; unfold "~" ; intros Hlt ; destruct Hlt.
      symmetry in e ; pose (eqv_impl_lte e) ; auto.
    - left ; auto.
    - right ; destruct l ; unfold "~" ; intros Hlt ; destruct Hlt ; auto.
    - right ; destruct u ; unfold "~" ; intros Hlt ; destruct Hlt ; auto.
  Qed.

  Definition un_dec x y :=
    match pord_dec x y with None => true | _ => false end.
  Definition un_dec_p (x:T) (y:T) : {un x y}+{~un x y}.
  Proof.
    pose (pord_dec_p x y) ;
    repeat match goal with
    | [ H : sumbool _ _ |- _ ] => destruct H
    | [ H : sumor _ _ |- _ ] => destruct H
    end.
    - right ; unfold "~" ; intros Hun ; destruct Hun.
      pose (eqv_impl_lte e) ; auto.
    - right ; destruct l ; unfold "~" ; intros Hun ; destruct Hun ; auto.
    - right ; destruct l ; unfold "~" ; intros Hun ; destruct Hun ; auto.
    - left ; auto.
    Qed.
End lt_un_dec.

Section PartialOrd.
  Context {T} `{! Eqv T ,! Lte T ,! ER_WF T ,! PartialOrd T}.

  Global Instance lt_Asymmetric : Asymmetric lt.
  Proof.
    unfold Asymmetric ; intros.
    destruct H,H0 ; contradiction.
  Qed.
End PartialOrd.

Module PartialOrdNotation.
  Notation "x < y"         := (lt x y)
    (at level 70, no associativity).
  Notation "x < y < z"     := (lt x y /\ lt y z)
    (at level 70, y at next level, no associativity).
  Notation "x > y"         := (lt y x)
    (at level 70, no associativity, only parsing).
  Notation "x > y > z"     := (lt z y /\ lt y x)
    (at level 70, y at next level, no associativity, only parsing).
  Notation "x >< y"        := (un x y)
    (at level 70, no associativity).

  Notation "x <! y"        := (lt_dec x y)
    (at level 35, no associativity).
  Notation "x <! y <! z"   := (lt_dec x y && lt_dec y z)
    (at level 35, y at next level, no associativity).
  Notation "x >! y"        := (lt_dec y x)
    (at level 35, no associativity, only parsing).
  Notation "x >! y >! z"   := (lt_dec z y && lt_dec y x)
    (at level 35, y at next level, no associativity).
  Notation "x ><! y"       := (un_dec x y)
    (at level 35, no associativity).
  Notation "x <~>! y"      := (pord_dec x y)
    (at level 35, no associativity).

  Notation "x <? y"        := (lt_dec_p x y)
    (at level 35, no associativity).
  Notation "x <? y <? z"   := (lt_dec_p x y /\ lt_dec_p y z)
    (at level 35, y at next level, no associativity).
  Notation "x >? y"        := (lt_dec_p y x)
    (at level 35, no associativity, only parsing).
  Notation "x >? y >? z"   := (lt_dec_p z y /\ lt_dec_p y x)
    (at level 35, y at next level, no associativity, only parsing).
  Notation "x ><? y"       := (un_dec_p x y)
    (at level 35, no associativity).
  Notation "x <~>? y"      := (pord_dec_p x y)
    (at level 35, no associativity).
End PartialOrdNotation.
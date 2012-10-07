Require Import Equivalence.

Require Import StdFun.
Import FunNotation.
Require Import RelDec.

Class Lte T := { lte : T -> T -> Prop }.
Section Lte.
  Context {T} {L:Lte T}.

  Definition not_lte := not <..> lte.
End Lte.

Class LteDec T := { lte_dec : T -> T -> bool }.
Section LteDec.
  Context {T} {LD:LteDec T}.

  Definition neg_lte_dec := negb <..> lte_dec.

  Context {L:Lte T}.

  Global Instance Lte_RelDec : RelDec lte_dec lte.

  Context {RDC:RelDecCorrect lte_dec lte}.

  Definition lte_dec_p : forall x y:T, {lte x y}+{~lte x y} := rel_dec_p.
  Definition neg_lte_dec_p : forall x y:T, {~lte x y}+{lte x y} := neg_rel_dec_p.
End LteDec.

Section Lt.
  Context {T} {L:Lte T}.

  Definition lt x y := lte x y /\ ~lte y x.
  Definition not_lt := not <..> lt.

  Context {PO:PreOrder lte}.

  Global Instance Lt_StrictOrder : StrictOrder lt.
  Admitted.
End Lt.

Section LtDec.
  Require Import Bool.
  Open Scope bool_scope.

  Context {T} {LD:LteDec T}.

  Definition lt_dec x y := lte_dec x y && negb (lte_dec y x).
  Definition neg_lt_dec := negb <..> lt_dec.

  Context {L:Lte T}.

  Global Instance Lt_RelDec : RelDec lt_dec lt.

  Context {RDC:RelDecCorrect lte_dec lte}.

  Global Instance Lt_RelDecCorrect : RelDecCorrect lt_dec lt.
  Proof. constructor ; constructor ; intros ; unfold lt in * ; unfold lt_dec in *.
    apply andb_true_iff in H ; destruct H ; constructor.
      apply rel_dec_correct ; auto.
      apply negb_true_iff in H0 ; apply neg_rel_dec_correct ; auto.
    destruct H ; apply andb_true_iff ; constructor.
      apply rel_dec_correct ; auto.
      apply negb_true_iff ; apply neg_rel_dec_correct ; auto.
  Qed.

  Definition lt_dec_p : forall x y:T, {lt x y}+{~lt x y} := rel_dec_p.
  Definition neg_lt_dec_p : forall x y:T, {~lt x y}+{lt x y} := neg_rel_dec_p.
End LtDec.

Section OrderEqv.
  Context {T} {L:Lte T}.

  Definition order_eqv x y := lte x y /\ lte y x.
  Definition not_order_eqv := not <..> order_eqv.

  Context {PO:PreOrder lte}.

  Global Instance order_eqv_Equivalence : Equivalence order_eqv. 
  Admitted.
End OrderEqv.

Section OrderEqvDec.
  Require Import Bool.
  Open Scope bool_scope.

  Context {T} {LD:LteDec T}.

  Definition order_eqv_dec x y := lte_dec x y && lte_dec y x.
  Definition neg_order_eqv_dec := negb <..> order_eqv_dec.

  Context {L:Lte T}.

  Global Instance OrderEqv_RelDec : RelDec order_eqv_dec order_eqv.

  Context {RDC:RelDecCorrect lte_dec lte}.

  Global Instance OrderEqv_RelDecCorrect : RelDecCorrect order_eqv_dec order_eqv.
  Admitted.

  Definition order_eqv_dec_p : forall x y:T, {order_eqv x y}+{~order_eqv x y} :=
    rel_dec_p.
  Definition neg_order_eqv_dec_p : forall x y:T, {~order_eqv x y}+{order_eqv x y} :=
    neg_rel_dec_p.

  Context {PO:PreOrder lte}.

  Global Instance OrderEqv_PreOrder : PreOrder order_eqv.
  Proof. constructor.
    unfold Reflexive ; intros ; unfold order_eqv.
      constructor ; reflexivity.
    unfold Transitive ; intros ; unfold order_eqv.
      inversion H ; inversion H0 ; subst ; clear H H0.
      constructor ; transitivity y ; auto.
  Qed.
End OrderEqvDec.

Module LteNotation.
  Notation "x '<= y"       := (lte x y)
    (at level 70, no associativity).
  Notation "x '<= y '<= z" := (lte x y /\ lte y z)
    (at level 70, y at next level, no associativity).
  Notation "x '>= y"       := (lte y x)
    (at level 70, no associativity, only parsing).
  Notation "x '>= y '>= z" := (lte z y /\ lte y x)
    (at level 70, y at next level, no associativity, only parsing).

  Notation "x '<=! y"       := (lte_dec x y)
    (at level 35, no associativity).
  Notation "x '<=! y '<=! z" := (lte_dec x y /\ lte_dec y z)
    (at level 35, y at next level, no associativity).
  Notation "x '>=! y"       := (lte_dec y x)
    (at level 35, no associativity, only parsing).
  Notation "x '>=! y '>=! z" := (lte_dec z y /\ lte_dec y x)
    (at level 35, y at next level, no associativity).

  Notation "x '<=? y"       := (lte_dec_p x y)
    (at level 35, no associativity).
  Notation "x '<=? y '<=? z" := (lte_dec_p x y /\ lte_dec_p y z)
    (at level 35, y at next level, no associativity).
  Notation "x '>=? y"       := (lte_dec_p y x)
    (at level 35, no associativity, only parsing).
  Notation "x '>=? y '>=? z" := (lte_dec_p z y /\ lte_dec_p y x)
    (at level 35, y at next level, no associativity, only parsing).

  Notation "x '< y"       := (lt x y)
    (at level 70, no associativity).
  Notation "x '< y '< z" := (lt x y /\ lt y z)
    (at level 70, y at next level, no associativity).
  Notation "x '> y"       := (lt y x)
    (at level 70, no associativity, only parsing).
  Notation "x '> y '> z" := (lt z y /\ lt y x)
    (at level 70, y at next level, no associativity, only parsing).

  Notation "x '<! y"       := (lt_dec x y)
    (at level 35, no associativity).
  Notation "x '<! y '<! z"  := (lt_dec x y /\ lt_dec y z)
    (at level 35, y at next level, no associativity).
  Notation "x '>! y"       := (lt_dec y x)
    (at level 35, no associativity, only parsing).
  Notation "x '>! y '>! z"  := (lt_dec z y /\ lt_dec y x)
    (at level 35, y at next level, no associativity).

  Notation "x '<? y"       := (lt_dec_p x y)
    (at level 35, no associativity).
  Notation "x '<? y '<? z"  := (lt_dec_p x y /\ lt_dec_p y z)
    (at level 35, y at next level, no associativity).
  Notation "x '>? y"       := (lt_dec_p y x)
    (at level 35, no associativity, only parsing).
  Notation "x '>? y '>? z"  := (lt_dec_p z y /\ lt_dec_p y x)
    (at level 35, y at next level, no associativity, only parsing).

  Notation "x '<=> y" := (order_eqv x y)
    (at level 70, no associativity).

  Notation "x '<=>! y" := (order_eqv_dec x y)
    (at level 35, no associativity).

  Notation "x '<=>? y" := (order_eqv_dec_p x y)
    (at level 35, no associativity).
End LteNotation.

(* Begin Context Aliases *)
Class LteWF T :=
{ wf_lte : Lte T
; wf_lte_pre_order : PreOrder lte
}.
Hint Immediate Build_LteWF : typeclass_instances.
Hint Immediate wf_lte : typeclass_instances.
Hint Immediate wf_lte_pre_order : typeclass_instances.

Class LteWithDec T :=
{ with_lte : Lte T
; with_lte_dec : LteDec T
}.
Hint Immediate Build_LteWithDec : typeclass_instances.
Hint Immediate with_lte : typeclass_instances.
Hint Immediate with_lte_dec : typeclass_instances.

Class LteWFWithDec T :=
{ with_lte_wf : LteWF T
; with_lte_dec_wf : LteDec T
}.
Hint Immediate Build_LteWFWithDec : typeclass_instances.
Hint Immediate with_lte_wf : typeclass_instances.
Hint Immediate with_lte_dec_wf : typeclass_instances.
(* End Context Aliases *)


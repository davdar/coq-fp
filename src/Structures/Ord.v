Require Import FP.Data.BoolPre.
Require Import FP.Structures.RelationClasses.

Require Import FP.Structures.Eqv.

Import BoolNotation.

Class Ord T :=
  { ord_Eqv :> Eqv T
  ; lt : T -> T -> Prop
  }.
Class OrdWF T {O:Ord T} :=
  { ord_wf_EqvWF :> EqvWF T
  ; lt_Irreflexive :> Irreflexive lt
  ; lt_Transitive :> Transitive lt
  ; lt_resp_eqv : forall t1 t2 t3 t4, eqv t1 t2 -> eqv t3 t4 -> lt t1 t3 -> lt t2 t4
  }.
                               
Class OrdDec T :=
  { ord_dec_EqvDec :> EqvDec T
  ; ord_dec : T -> T -> comparison
  }.

Section Ord.
  Context {T} {O:Ord T}.

  Definition lte x y := lt x y \/ eqv x y.

  Context {WF:OrdWF T}.

  Global Instance lt_Asymmetric : Asymmetric lt.
    unfold Asymmetric.
    intros.
    apply (lt_Irreflexive x).
    transitivity y ; auto.
    Qed.
  Global Instance lte_Reflexive : Reflexive lte.
    unfold Reflexive.
    intros.
    unfold lte.
    right.
    reflexivity.
    Qed.
  Global Instance lte_Transitive : Transitive lte.
    unfold Transitive.
    intros * * * e1 e2.
    destruct e1 as [e1 | e1], e2 as [e2 | e2].
    left ; transitivity y ; auto.
    left ; apply (lt_resp_eqv x x y z) ; auto ; reflexivity.
    left ; apply (lt_resp_eqv y x z z) ; auto ; symmetry ; auto ; reflexivity.
    right ; transitivity y ; auto.
    Qed.
  Global Instance lte_Antisymmetric : Antisymmetric T eqv lte.
    unfold Antisymmetric.
    intros * * e1 e2.
    destruct e1 as [e1 | e1], e2 as [e2 | e2] ; auto.
    exfalso.
      apply (lt_Asymmetric x y) ; auto.
    exfalso.
      apply (lt_Asymmetric x y) ; auto.
      apply (lt_resp_eqv x y y x) ; [symmetry ; auto | auto | auto].
    Qed.
End Ord.

Section OrdDec.
  Context {T} {tOD:OrdDec T}.

  Definition lt_dec x y :=
    match ord_dec x y with Lt => true  | Eq => false | Gt => false end.
  Definition lte_dec x y :=
    match ord_dec x y with Lt => true  | Eq => true  | Gt => false end.

  Context {tO:Ord T}.

  Definition ord_dec_p (x:T) (y:T) : {lt x y}+{eqv x y}+{lt y x}. Admitted.
  Definition lt_dec_p (x:T) (y:T) : {lt x y}+{~lt x y}. Admitted.
  Definition lte_dec_p (x:T) (y:T) : {lte x y}+{~lte x y}. Admitted.
  
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
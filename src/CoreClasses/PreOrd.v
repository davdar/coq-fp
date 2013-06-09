Require Import FP.CoreClasses.Setoid.
Require Import FP.CoreClasses.RelDec.
Require Import FP.CoreData.Bool.

Import BoolNotation.

Class Lte T := { lte : T -> T -> Prop }.
Arguments lte {T Lte} _ _ : simpl never.
Class PreOrd T `{! Lte T } :=
  { PreOrd_Reflexivity :> Reflexive lte
  ; PreOrd_Transitivity :> Transitive lte
  }.
Class LteDec T := { lte_dec : T -> T -> bool }.
Class Lte_RDC T `{! Lte T ,! LteDec T } := { lte_rdc :> RelDecCorrect T lte lte_dec }.

Section PreOrd.
  Context {T} `{! Lte T ,! LteDec T ,! Lte_RDC T }.
  Definition lte_dec_p : forall x y, {lte x y}+{~lte x y} := rel_dec_p.
End PreOrd.

Section lt_un.
  Context {T} `{! Lte T }.

  Definition lt x y := lte x y /\ ~lte y x.
  Definition un x y := ~lte x y /\ ~lte y x.

  Context `{! PreOrd T }.

  Global Instance lt_Transitive : Transitive lt.
  Proof.
    unfold Transitive ; intros.
    destruct H,H0.
    constructor.
    - transitivity y ; auto.
    - unfold "~" in * ; intros ; apply H1.
      transitivity z ; auto.
  Qed.

  Lemma lt_trans_lte : forall {x} y {z}, lte y z -> lt x y -> lt x z.
  Proof.
    intros * * * H H1 ; destruct H1 as [Hlt Hnlt] ; constructor.
    - transitivity y ; auto.
    - unfold "~" ; intros H2 ; apply Hnlt ; transitivity z ; auto.
  Qed.

  Lemma lte_trans_lt : forall {x} y {z}, lte x y -> lt y z -> lt x z.
  Proof.
    intros * * * H H1 ; destruct H1 as [Hlt Hnlt] ; constructor.
    - transitivity y ; auto.
    - unfold "~" ; intros H2 ; apply Hnlt ; transitivity x ; auto.
  Qed.
End lt_un.

Module PreOrdNotation.
  Notation "x <= y"        := (lte x y)
    (at level 70, no associativity).
  Notation "x <= y <= z"   := (lte x y /\ lte y z)
    (at level 70, y at next level, no associativity).
  Notation "x >= y"        := (lte y x)
    (at level 70, no associativity, only parsing).
  Notation "x >= y >= z"   := (lte z y /\ lte y x)
    (at level 70, y at next level, no associativity, only parsing).

  Notation "x <=! y"       := (lte_dec x y)
    (at level 35, no associativity).
  Notation "x <=! y <=! z" := (lte_dec x y && lte_dec y z)
    (at level 35, y at next level, no associativity).
  Notation "x >=! y"       := (lte_dec y x)
    (at level 35, no associativity, only parsing).
  Notation "x >=! y >=! z" := (lte_dec z y && lte_dec y x)
    (at level 35, y at next level, no associativity, only parsing).

  Notation "x <=? y"       := (lte_dec_p x y)
    (at level 35, no associativity).
  Notation "x <=? y <=? z" := (lte_dec_p x y /\ lte_dec_p y z)
    (at level 35, y at next level, no associativity).
  Notation "x >=? y"       := (lte_dec_p y x)
    (at level 35, no associativity, only parsing).
  Notation "x >=? y >=? z" := (lte_dec_p z y /\ lte_dec_p y x)
    (at level 35, y at next level, no associativity, only parsing).
End PreOrdNotation.
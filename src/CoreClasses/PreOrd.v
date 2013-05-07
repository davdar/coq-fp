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
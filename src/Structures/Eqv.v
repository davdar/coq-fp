Require Import Data.FunctionPre.

Require Import Relations.RelDec.
Require Import Structures.RelationClasses.

Import FunctionNotation.

Class Eqv T := { eqv : T -> T -> Prop }.
Section Eqv.
  Context {T} {E:Eqv T}.

  Definition not_eqv : T -> T -> Prop := not <..> eqv.
End Eqv.

Class EqvDec T := { eqv_dec : T -> T -> bool }.
Section EqvDec.
  Context {T} {ED:EqvDec T}.

  Definition neg_eqv_dec : T -> T -> bool := negb <..> eqv_dec.

  Context {E:Eqv T}.

  Global Instance Eqv_RelDec : RelDec eqv_dec eqv.

  Context {RDC:RelDecCorrect eqv_dec eqv}.

  Definition eqv_dec_p : forall x y:T, {eqv x y} + {~eqv x y} := rel_dec_p.
  Definition neg_eqv_dec_p : forall x y:T, {~eqv x y} + {eqv x y} := neg_rel_dec_p.
End EqvDec.

Module EqvNotation.
  Infix "'~=!" := eqv_dec (at level 35, no associativity).
  Infix "'/~=!" := neg_eqv_dec (at level 35, no associativity).

  Infix "'~=?" := eqv_dec_p (at level 35, no associativity).
  Infix "'/~=?" := neg_eqv_dec_p (at level 35, no associativity).

  Infix "'~=" := eqv (at level 70, no associativity).
  Infix "'/~=" := not_eqv (at level 70, no associativity).
End EqvNotation.
Import EqvNotation.

(* Begin Context Aliases *)
Class EqvWF T :=
{ wf_eqv : Eqv T
; wf_eqv_equivalence : Equivalence eqv
}.
Hint Immediate Build_EqvWF : typeclass_instances.
Hint Immediate wf_eqv : typeclass_instances.
Hint Immediate wf_eqv_equivalence : typeclass_instances.

Class EqvWithDec T :=
{ with_eqv : Eqv T
; with_eqv_dec : EqvDec T
}.
Hint Immediate Build_EqvWithDec : typeclass_instances.
Hint Immediate with_eqv : typeclass_instances.
Hint Immediate with_eqv_dec : typeclass_instances.

Class EqvWFWithDec T :=
{ with_eqv_wf : EqvWF T
; with_eqv_dec_wf : EqvDec T
}.
Hint Immediate Build_EqvWFWithDec : typeclass_instances.
Hint Immediate with_eqv_wf : typeclass_instances.
Hint Immediate with_eqv_dec_wf : typeclass_instances.
(* End Context Aliases *)

Section morph_eqv_Equivalence.
  Context {T U} {TEWF:EqvWF T} {UE:EqvWF U}.
  Variable morph:U -> T.
  Variable morph_resp : forall u1 u2, u1 '~= u2 <-> morph u1 '~= morph u2.

  Definition morph_eqv_Equivalence : Equivalence (eqv (T:=U)).
  Proof. repeat constructor ;
    unfold Reflexive ; unfold Symmetric ; unfold Transitive ; intros.
    apply morph_resp. reflexivity.
    apply morph_resp. apply morph_resp in H. symmetry. auto.
    apply morph_resp. apply morph_resp in H. apply morph_resp in H0.
    transitivity (morph y) ; auto.
  Qed.
End morph_eqv_Equivalence.
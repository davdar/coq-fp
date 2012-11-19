Require Import Data.BoolPre.

Section RelDec.
  Context {T:Type}.
  
  Class RelDec (D:T -> T -> bool) (R:T -> T -> Prop) : Type := {}.

  Class RelDecCorrect (D:T -> T -> bool) (R: T -> T -> Prop) : Prop :=
    { rel_dec_correct : forall {x y}, D x y = true <-> R x y }.

  (* Context Alias *)
  Class RelDecWithCorrect D R : Type :=
  { with_rel_dec : RelDec D R
  ; with_rel_dec_correct : RelDecCorrect D R
  }.
End RelDec.
Hint Immediate Build_RelDecWithCorrect : typeclass_instances.
Hint Immediate with_rel_dec : typeclass_instances.
Hint Immediate with_rel_dec_correct : typeclass_instances.

Section neg_rel_dec_correct.
  Context {T D R} {RDC:RelDecWithCorrect (T:=T) D R}.

  Definition neg_rel_dec_correct : forall {x y}, D x y = false <-> ~R x y.
  Proof. intros x y. destruct (consider_bool (D x y)) ; constructor ; intros ;
    repeat
      match goal with
      | [ |- ~ _ ] => unfold not ; intros
      | [ H1 : ?P, H2 : ~?P |- _ ] => specialize (H2 H1) ; contradiction
      | [ H1 : ?P = true, H2 : ?P = false |- _ ] => rewrite H1 in H2 ; discriminate
      | [ H1 : ?P <> true |- ?P = false ] => apply not_true_is_false ; exact H1
      | [ H1 : ?rel_dec ?a ?b = true, H2 : ~?R ?a ?b |- _ ] =>
          apply rel_dec_correct in H1
      | [ H1 : ?rel_dec ?a ?b = false, H2 : ?R ?a ?b |- _ ] =>
          apply rel_dec_correct in H2
      end ; eauto.
  Qed.
End neg_rel_dec_correct.

Section rel_dec_p.
  Context {T D R} {RDWC:RelDecWithCorrect (T:=T) D R}.

  Definition rel_dec_p (x:T) (y:T) : {R x y} + {~R x y}.
  Proof. destruct (consider_bool (D x y)) as [H | H].
    apply rel_dec_correct in H ; eauto.
    apply neg_rel_dec_correct in H ; eauto.
  Qed.

  Definition neg_rel_dec_p (x:T) (y:T) : {~R x y} + {R x y}.
  Proof. destruct (rel_dec_p x y) ; [ right | left ] ; auto. Qed.
End rel_dec_p.

Section morph_RelDec.
  Context {T U} D R {RD:RelDec (T:=T) D R} (morph:U -> T).

  Definition morph_dec (x:U) (y:U) : bool := D (morph x) (morph y).
  Definition morph_rel (x:U) (y:U) : Prop := R (morph x) (morph y).
  Definition morph_RelDec : RelDec morph_dec morph_rel. constructor. Defined.

  Context {RDC:RelDecCorrect D R}.

  Definition morph_RelDecCorrect : RelDecCorrect morph_dec morph_rel.
  Proof. constructor ; intros ;
    unfold morph_dec in * ; unfold morph_rel in * ; apply rel_dec_correct ; auto.
  Qed.
End morph_RelDec.

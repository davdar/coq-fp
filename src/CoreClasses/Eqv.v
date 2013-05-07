Require Import FP.CoreData.Function.
Require Import FP.CoreClasses.RelDec.
Require Import FP.CoreClasses.Injection.
Require Import FP.CoreClasses.Setoid.

Import FunctionNotation.
Import ProperNotation.

Class Eqv T := { eqv : T -> T -> Prop }.
Arguments eqv {T Eqv} _ _ : simpl never.
Class PER_WF T `{! Eqv T } := { per_wf :> PER eqv }.
Class ER_WF T `{! Eqv T } := { er_wf :> Equivalence eqv }.
Class EqvDec T := { eqv_dec : T -> T -> bool }.
Class Eqv_RDC T `{! Eqv T ,! EqvDec T } := { eqv_rdc :> RelDecCorrect T eqv eqv_dec }.

Section Eqv.
  Context {T} `{! Eqv T }.

  Definition not_eqv : T -> T -> Prop := not '.:' eqv.
End Eqv.

Section EqvDec.
  Context {T} `{! EqvDec T }.

  Definition neg_eqv_dec : T -> T -> bool := negb '.:' eqv_dec.

  Context `{! Eqv T ,! Eqv_RDC T }.

  Definition eqv_dec_p : forall x y:T, {eqv x y} + {~eqv x y} := rel_dec_p.
  Definition neg_eqv_dec_p : forall x y:T, {~eqv x y} + {eqv x y} := neg_rel_dec_p.
End EqvDec.
Arguments eqv_dec {T EqvDec} _ _ : simpl never.

(* Logical equivalence *)

Module EqvNotation.
  Infix "~=!" := eqv_dec (at level 35, no associativity).
  Infix "/~=!" := neg_eqv_dec (at level 35, no associativity).

  Infix "~=?" := eqv_dec_p (at level 35, no associativity).
  Infix "/~=?" := neg_eqv_dec_p (at level 35, no associativity).

  Infix "~=" := eqv (at level 70, no associativity).
  Infix "/~=" := not_eqv (at level 70, no associativity).
End EqvNotation.
Section Fun_Eqv.
  Context {A} `{! Eqv A }.
  Context {B} `{! Eqv B }.

  Definition fun_eqv : (A -> B) -> (A -> B) -> Prop := eqv ==> eqv.
  Global Instance Fun_Eqv : Eqv (A -> B) := { eqv := fun_eqv }.
  Definition fun_eqv_intro {f:A -> B} {g:A -> B} : (eqv ==> eqv) f g -> eqv f g := id.
  Definition fun_eqv_elim {f:A -> B} {g:A -> B} : eqv f g -> (eqv ==> eqv) f g := id.
  Global Opaque fun_eqv.
End Fun_Eqv.

Ltac logical_eqv_intro_once :=
  match goal with
  | [ |- eqv ?A ?B ] =>
      match type of A with
      | ?T -> ?U => apply fun_eqv_intro ; unfold "==>" at 1 ; intros
      | Fun ?T ?U => apply fun_eqv_intro ; unfold "==>" at 1 ; intros
      end
  end.

Ltac logical_eqv_intro := repeat logical_eqv_intro_once.
Ltac logical_eqv_elim_once :=
  match goal with
  | [ |- eqv (?f ?x) (?g ?y) ] => apply fun_eqv_elim
  end.
Ltac logical_eqv_elim := repeat logical_eqv_elim_once.

Create HintDb logical_eqv_db.

Ltac logical_eqv_once :=
  match goal with
  | [ |- eqv (?f ?x) (?g ?y) ] =>
      let g_type := type of g in
      match type of f with
      | g_type => apply fun_eqv_elim
      end
  | [ |- eqv (fun _ => _) _ ] =>
      apply fun_eqv_intro ; unfold "==>" at 1 ; intros
  | [ |- eqv _ (fun _ => _) ] =>
      apply fun_eqv_intro ; unfold "==>" at 1 ; intros
  end.
Ltac logical_eqv :=
  match goal with
  | [ |- Proper eqv ?x ] => unfold Proper
  | _ => idtac
  end ;
  repeat logical_eqv_once ;
  match goal with
  | [ |- eqv ?x ?x ] => change (eqv x x) with (Proper eqv x)
  | _ => idtac
  end ;
  eauto with logical_eqv_db typeclass_instances.

Section Fun_WFPER.
  Context {A} `{! Eqv A ,! PER_WF A}.
  Context {B} `{! Eqv B ,! PER_WF B}.

  Global Instance Fun_WFPER : PER_WF (A -> B).
  Proof.
    repeat constructor.
    - unfold Symmetric ; intros.
      logical_eqv_intro.
      symmetry ; auto.
      logical_eqv_elim ; auto.
      symmetry ; auto.
    - unfold Transitive ; intros.
      logical_eqv_intro.
      transitivity (y x0).
      logical_eqv_elim ; auto.
      transitivity y0 ; auto.
      symmetry ; auto.
      logical_eqv_elim ; auto.
  Qed.
End Fun_WFPER.

Section Eqv_Logical.
  Context {A} `{! Eqv A ,! PER_WF A }.
  Context {B} `{! Eqv B }.
  Context {C} `{! Eqv C }.
  Context {D} `{! Eqv D }.

  Global Instance Proper_PER_elim1 {f:A -> B} `{! Proper eqv f }
    : Proper (eqv ==> eqv) f := Proper0.
  Global Instance Proper_PER_elim2 {f:A -> B -> C} `{! Proper eqv f }
    : Proper (eqv ==> eqv ==> eqv) f := Proper0.
  Global Instance Proper_PER_elim3 {f:A -> B -> C -> D} `{! Proper eqv f }
    : Proper (eqv ==> eqv ==> eqv ==> eqv) f := Proper0.
  Global Instance Proper_app (f:A -> B) `(! Proper eqv f ) (a:A) `(! Proper eqv a )
    : Proper eqv (f a) := Proper0 a a Proper1.
  Global Instance per_Proper_left (x:A) (y:A) `(! eqv x y ) : Proper eqv x.
  Proof.
    unfold Proper.
    transitivity y ; auto.
    symmetry ; auto.
  Qed.
  Global Instance per_Proper_right (x:A) (y:A) `(! eqv x y ) : Proper eqv y.
  Proof.
    unfold Proper.
    transitivity x ; auto.
    symmetry ; auto.
  Qed.
End Eqv_Logical.

Section Injection.
  Context {T U} `{! Eqv T ,! Eqv U }.

  Global Instance Proper_inj {inj} `{! InjectionRespect T U inj eqv eqv }
    : Proper eqv inj.
  Proof.
    unfold Proper ; apply fun_eqv_intro.
    apply InjectionRespect_eta.
  Qed.
End Injection.

Section Function.
  Context {A} `{! Eqv A ,! PER_WF A }.
  Context {B} `{! Eqv B ,! PER_WF B }.
  Context {C} `{! Eqv C ,! PER_WF C }.

  Global Instance id_Proper : Proper eqv (id (A:=A)).
  Proof.
    unfold Proper ; logical_eqv_intro ; auto.
  Qed.

  Global Instance compose_Proper : Proper eqv (compose (A:=A) (B:=B) (C:=C)).
  Proof.
    unfold Proper ; logical_eqv_intro ; simpl ; logical_eqv.
  Qed.

  Global Instance const_Proper : Proper eqv (const (A:=A)).
  Proof.
    unfold Proper ; logical_eqv_intro ; auto.
  Qed.

  Global Instance apply_Proper : Proper eqv (apply (A:=A) (B:=B)).
  Proof.
    unfold Proper ; logical_eqv_intro ; simpl ; logical_eqv.
  Qed.

  Global Instance apply_to_Proper : Proper eqv (apply_to (A:=A) (B:=B)).
  Proof.
    unfold Proper ; logical_eqv_intro ; simpl ; logical_eqv.
  Qed.

End Function.
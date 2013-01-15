Require Import FP.Data.Function.

Require Import FP.Relations.RelDec.
Require Import FP.Structures.RelationClasses.
Require Import FP.Structures.Injection.

Import FunctionNotation.

Class Eqv T := { eqv : T -> T -> Prop }.
Section Eqv.
  Context {T} {E:Eqv T}.

  Definition not_eqv : T -> T -> Prop := not '..' eqv.
End Eqv.

Class EqvWF T {E:Eqv T} :=
  { eqv_equivalence :> Equivalence eqv
  }.

Class EqvDec T := { eqv_dec : T -> T -> bool }.
Section EqvDec.
  Context {T} {ED:EqvDec T}.

  Definition neg_eqv_dec : T -> T -> bool := negb '..' eqv_dec.

  Context {E:Eqv T}.

  Global Instance Eqv_RelDec : RelDec eqv_dec eqv.

  Context {RDC:RelDecCorrect eqv_dec eqv}.

  Definition eqv_dec_p : forall x y:T, {eqv x y} + {~eqv x y} := rel_dec_p.
  Definition neg_eqv_dec_p : forall x y:T, {~eqv x y} + {eqv x y} := neg_rel_dec_p.
End EqvDec.

Module EqvNotation.
  Infix "~=!" := eqv_dec (at level 35, no associativity).
  Infix "/~=!" := neg_eqv_dec (at level 35, no associativity).

  Infix "~=?" := eqv_dec_p (at level 35, no associativity).
  Infix "/~=?" := neg_eqv_dec_p (at level 35, no associativity).

  Infix "~=" := eqv (at level 70, no associativity).
  Infix "/~=" := not_eqv (at level 70, no associativity).
End EqvNotation.
Import EqvNotation.

Section inj_eqv_Equivalence.
  Context {T U minj}
          {TE:Eqv T} {UE:Eqv U} {TEWF:EqvWF T}
          {Bij:Injection U T minj}
          {BijR:InjectionRespect U T minj eqv eqv}.

  Definition inj_eqv_Equivalence : Equivalence (eqv (T:=U)).
    Ltac mysimp :=
      match goal with
      | [ x : U |- ?x ~= ?x ] => apply (inject_resp_beta (mor:=minj))
      | [ x : U, y : U |- ?x ~= ?y ] => apply (inject_resp_beta (mor:=minj))
      | [ x : U, y : U, H : ?x ~= ?y |- _ ] => apply (inject_resp_eta (mor:=minj)) in H
      | _ => auto
      end.
    constructor.
    unfold Reflexive ; intros ; repeat mysimp ; reflexivity.
    unfold Symmetric ; intros ; repeat mysimp ; symmetry ; auto.
    unfold Transitive ; intros x y z t1 t2 ; repeat mysimp ;
      transitivity (minj y) ; auto.
  Qed.
End inj_eqv_Equivalence.
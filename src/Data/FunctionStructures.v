Require Import FP.Data.Function.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.EqvRel.
Require Import FP.Relations.Setoid.
Require Import FP.Structures.Category.
Require Import FP.Structures.Proxy.
Require Import FP.Structures.Eqv.

Import FunctionNotation.
Import ProperNotation.

Section Category.
  Global Instance fun_Category : Category Fun :=
    { cid := @id
    ; ccompose := @compose
    }.

  Global Instance fun_CategoryWF_eq : CategoryWF Fun (EqvEnv_:=eq_EqvEnv).
  Proof.
    constructor ; intros ; simpl in * ; subst ; auto.
  Qed.
End Category.

Ltac promote_fun_once :=
  match goal with
  | [ |- context [ ?x ] ] =>
      match x with
      | id =>
          match type of x with ?A->?A =>
            change id
            with (cid (t:=Fun) (A:=A))
          end
      end
  | [ |- appcontext [ ?x ] ] =>
      match x with
      | compose =>
          match type of x with (?B->?C)->(?A->?B)->?A->?C =>
            change (compose (A:=A) (B:=B) (C:=C))
            with (ccompose (t:=Fun) (A:=A) (B:=B) (C:=C))
          end
      end
  end.
Ltac promote_fun := repeat promote_fun_once.

Section id_respect.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvWF_:EqvEnvWF}.
  Context {A} {aPER:PE_R A}.
  Global Instance id_respect : Proper PE_eqv id.
  Proof.
    unfold Proper.
    logical_eqv_intro ; auto.
  Qed.
End id_respect.
Hint Immediate id_respect : logical_eqv_db.

Section compose_respect.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvWF_:EqvEnvWF}.
  Context {A} {aPER:PE_R A}.
  Context {B} {bPER:PE_R B}.
  Context {C} {cPER:PE_R C}.
  Global Instance compose_respect : Proper PE_eqv (compose (A:=A) (B:=B) (C:=C)).
  Proof.
    unfold Proper.
    logical_eqv_intro ; simpl ; logical_eqv_elim ; auto.
  Qed.
End compose_respect.
Hint Immediate compose_respect : logical_eqv_db.

Definition compose_associativity :
  forall
    {A B C D}
    (f:A -> B) (g:B -> C) (h:C -> D),
      h '.' g '.' f = ((h '.' g) '.' f).
Proof. auto. Qed.

Section const_respect.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvWF_:EqvEnvWF}.
  Context {A} {aPER:PE_R A}.
  Global Instance const_respect : Proper PE_eqv (const (A:=A)).
  Proof.
    unfold Proper.
    logical_eqv_intro ; auto.
  Qed.
End const_respect.
Hint Immediate const_respect : logical_eqv_db.

Section apply_respect.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvWF_:EqvEnvWF}.
  Context {A} {aPER:PE_R A}.
  Context {B} {bPER:PE_R B}.
  Global Instance apply_respect : Proper PE_eqv apply.
  Proof.
    unfold Proper.
    logical_eqv_intro ; simpl ; logical_eqv_elim ; auto.
  Qed.
End apply_respect.
Hint Immediate apply_respect : logical_eqv_db.
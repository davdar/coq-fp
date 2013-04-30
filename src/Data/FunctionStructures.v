Require Import FP.Data.Function.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Feq.
Require Import FP.Structures.EqvEnv.
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

  Section fun_CategoryWF_eq.
    Local Instance EqvEnv_ : EqvEnv := feq_EqvEnv.
    Local Instance EqvEnvLogical_ : EqvEnvLogical := feq_EqvEnvLogical.
    Global Instance fun_CategoryWF_eq : CategoryWF Fun.
    Proof.
      constructor ; intros ; unfold ccompose,cid ; simpl ; logical_eqv.
      logical_eqv_intro ; simpl ; logical_eqv.
    Qed.
  End fun_CategoryWF_eq.
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
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {A} {aPER:Px (env_PER A)} {aPER':Px (env_PER_WF A)}.
  Global Instance id_respect : Proper env_eqv id.
  Proof.
    logical_eqv_intro ; auto.
  Qed.
End id_respect.

Section compose_respect.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {A} {aPER:Px (env_PER A)} {aPER':Px (env_PER_WF A)}.
  Context {B} {bPER:Px (env_PER B)} {bPER':Px (env_PER_WF B)}.
  Context {C} {cPER:Px (env_PER C)} {cPER':Px (env_PER_WF C)}.
  Global Instance compose_respect : Proper env_eqv (compose (A:=A) (B:=B) (C:=C)).
  Proof.
    logical_eqv_intro ; simpl ; logical_eqv.
  Qed.
End compose_respect.

Definition compose_associativity :
  forall
    {A B C D}
    (f:A -> B) (g:B -> C) (h:C -> D),
      h '.' g '.' f = ((h '.' g) '.' f).
Proof. auto. Qed.

Section const_respect.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {A} {aPER:Px (env_PER A)} {aPER':Px (env_PER_WF A)}.
  Global Instance const_respect : Proper env_eqv (const (A:=A)).
  Proof.
    logical_eqv_intro ; auto.
  Qed.
End const_respect.

Section apply_respect.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {A} {aPER:Px (env_PER A)} {aPER':Px (env_PER_WF A)}.
  Context {B} {bPER:Px (env_PER B)} {bPER':Px (env_PER_WF B)}.
  Global Instance apply_respect : Proper env_eqv (apply (A:=A) (B:=B)).
  Proof.
    logical_eqv_intro ; simpl ; logical_eqv.
  Qed.
End apply_respect.

Section apply_to_respect.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.
  Context {A} {aPER:Px (env_PER A)} {aPER':Px (env_PER_WF A)}.
  Context {B} {bPER:Px (env_PER B)} {bPER':Px (env_PER_WF B)}.
  Global Instance apply_to_respect : Proper env_eqv (apply_to (A:=A) (B:=B)).
  Proof.
    logical_eqv_intro ; simpl ; logical_eqv.
  Qed.
End apply_to_respect.
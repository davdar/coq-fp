Require Import FP.Data.Function.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.Injection.
Require Import FP.Structures.EqvEnv.
Require Import FP.Structures.Proxy.
Require Import FP.Relations.Setoid.

Import FunctionNotation.
Import ProperNotation.

Class Eqv T := { eqv : T -> T -> Prop }.

Arguments eqv {T Eqv} _ _ : simpl never.

Definition Eqv_Px {T} {Eqv_:Eqv T} : Px (Eqv T) := Eqv_.
Definition Px_Eqv {T} {Px_:Px (Eqv T)} : Eqv T := Px_.
Hint Resolve Eqv_Px : typeclass_instances.
Hint Immediate Px_Eqv : typeclass_instances.

Section Eqv.
  Context {T} {Eqv_:Eqv T}.

  Definition not_eqv : T -> T -> Prop := not '..' eqv.
End Eqv.

Class Eqv_E_WF T {Eqv_:Eqv T} := { eqv_E_WF :> Equivalence eqv }.
Class Eqv_PE_WF T {Eqv_:Eqv T} := { eqv_PE_WF :> PER eqv }.

Definition Eqv_PE_WF_Px {T} {Eqv_:Eqv T} {Eqv_PE_WF_:Eqv_PE_WF T}
    : Px (Eqv_PE_WF T) := Eqv_PE_WF_.
Definition Px_Eqv_PE_WF {T} {Eqv_:Px (Eqv T)} {Px_:Px (Eqv_PE_WF T)}
    : Eqv_PE_WF T := Px_.
Hint Resolve Eqv_PE_WF_Px : typeclass_instances.
Hint Immediate Px_Eqv_PE_WF : typeclass_instances.

Definition eqv_EqvEnv : EqvEnv :=
  {| env_PER := Eqv
  ;  env_eqv := fun T (p:Px (Eqv T)) => eqv
  ;  env_PER_WF := fun T (p:Px (Eqv T)) => Eqv_PE_WF T
  ;  env_eqv_WF := fun T (p:Px (Eqv T)) (pwf:Px (Eqv_PE_WF T)) => eqv_PE_WF
  |}.
Section EqvEnv.
  Local Instance EqvEnv_ : EqvEnv := eqv_EqvEnv.
  Global Instance env_eqv_WF_eqv {T} {p:Eqv T} {pwf:Eqv_PE_WF T} : PER env_eqv.
  Proof.
    pose (@env_eqv_WF _ T).
    auto.
  Qed.
End EqvEnv.

Section Fun_Eqv.
  Context {A} {aF:Eqv A} {B} {bF:Eqv B}.
  Local Instance Fun_Eqv : Eqv (A -> B) :=
    { eqv := (eqv ==> eqv) }.

  Variable (aPEWF:Eqv_PE_WF A) (bPEWF:Eqv_PE_WF B).
  Local Instance Fun_Eqv_PE_WF : Eqv_PE_WF (A -> B).
  Proof.
    inversion aPEWF ; inversion bPEWF.
    repeat econstructor.
    - unfold Symmetric ; eapply symmetry.
    - unfold Transitive ; eapply transitivity.
  Qed.
End Fun_Eqv.

Section Eqv_EqvEnvLogical.
  Local Instance EqvEnv2_ : EqvEnv := eqv_EqvEnv.
  Definition eqv_EqvEnvLogical : EqvEnvLogical.
  Proof.
    econstructor ; intros.
    apply Fun_Eqv_PE_WF ; auto.
    simpl ; auto.
    simpl in H ; auto.
  Qed.
End Eqv_EqvEnvLogical.

Section EqvEnvLogical.
  Local Instance EqvEnv3_ : EqvEnv := eqv_EqvEnv.
  Local Instance EqvEnvLogical_ : EqvEnvLogical := eqv_EqvEnvLogical.
  Global Instance eqv_env_logical_P_eqv :
    forall
      {A} {aP:Eqv A}
      {B} {bP:Eqv B},
    Eqv (A -> B).
  Proof.
    intros.
    pose (@eqv_env_logical_P _ _ A _ B _).
    auto.
  Defined.
  Global Instance eqv_env_logical_PE_WF :
    forall
      {A} {aP:Eqv A} {aPWF:Eqv_PE_WF A}
      {B} {bP:Eqv B} {bPWF:Eqv_PE_WF B},
    Eqv_PE_WF (A -> B).
  Proof.
    intros.
    assert (Px (Eqv_PE_WF A)) ; eauto with typeclass_instances.
    assert (Px (Eqv_PE_WF B)) ; eauto with typeclass_instances.
    pose (@eqv_env_logical_PE_WF _ _ A _ _ B _ _).
    auto.
  Qed.
  Definition eqv_env_logical_intro_eqv :
    forall
      {A} {aP:Eqv A}
      {B} {bP:Eqv B}
      {f:A -> B} {g:A -> B},
    (eqv ==> eqv) f g -> eqv f g.
  Proof.
    intros.
    pose (@eqv_env_logical_intro _ _).
    unfold env_eqv in e ; simpl in e.
    eauto.
  Qed.
  Definition eqv_env_logical_elim_eqv :
    forall
      {A} {aP:Eqv A}
      {B} {bP:Eqv B}
      {f:A -> B} {g:A -> B},
    eqv f g -> (eqv ==> eqv) f g.
  Proof.
    intros.
    pose (@eqv_env_logical_elim _ _).
    eauto.
  Qed.
End EqvEnvLogical.

Ltac logical_eqv_intro_once_eqv :=
  match goal with
  | [ |- eqv ?A ?B ] =>
      match type of A with
      | ?T -> ?U => apply eqv_env_logical_intro_eqv ; unfold "==>" at 1 ; intros
      | Fun ?T ?U => apply eqv_env_logical_intro_eqv ; unfold "==>" at 1 ; intros
      end
  end.

Ltac logical_eqv_intro_eqv := repeat logical_eqv_intro_once_eqv.
Ltac logical_eqv_elim_once_eqv :=
  match goal with
  | [ |- eqv (?f ?x) (?g ?y) ] => apply eqv_env_logical_elim_eqv
  end.
Ltac logical_eqv_elim_eqv := repeat logical_eqv_elim_once_eqv.

Create HintDb logical_eqv_db_eqv.

Ltac logical_eqv_once_eqv :=
  match goal with
  | [ |- eqv (?f ?x) (?g ?y) ] =>
      let g_type := type of g in
      match type of f with
      | g_type => logical_eqv_elim_once_eqv
      end
  | [ |- eqv (fun _ => _) _ ] =>
      logical_eqv_intro_once_eqv
  | [ |- eqv _ (fun _ => _) ] =>
      logical_eqv_intro_once_eqv
  end.
Ltac logical_eqv_eqv :=
  match goal with
  | [ |- Proper eqv ?x ] => unfold Proper
  | _ => idtac
  end ;
  repeat logical_eqv_once_eqv ;
  match goal with
  | [ |- eqv ?x ?x ] => change (eqv x x) with (Proper eqv x)
  | _ => idtac
  end ;
  eauto with logical_eqv_db_eqv typeclass_instances.

Class EqvDec T := { eqv_dec : T -> T -> bool }.
Section EqvDec.
  Context {T} {T_EqvDec:EqvDec T}.

  Definition neg_eqv_dec : T -> T -> bool := negb '..' eqv_dec.

  Context {T_Eqv:Eqv T}.

  Context {eqv_RDC:RelDecCorrect T eqv eqv_dec}.

  Definition eqv_dec_p : forall x y:T, {eqv x y} + {~eqv x y} := rel_dec_p.
  Definition neg_eqv_dec_p : forall x y:T, {~eqv x y} + {eqv x y} := neg_rel_dec_p.
End EqvDec.
Arguments eqv_dec {T EqvDec} _ _ : simpl never.

Module EqvNotation.
  Infix "~=!" := eqv_dec (at level 35, no associativity).
  Infix "/~=!" := neg_eqv_dec (at level 35, no associativity).

  Infix "~=?" := eqv_dec_p (at level 35, no associativity).
  Infix "/~=?" := neg_eqv_dec_p (at level 35, no associativity).

  Infix "~=" := eqv (at level 70, no associativity).
  Infix "/~=" := not_eqv (at level 70, no associativity).
End EqvNotation.
Import EqvNotation.
Require Import FP.Data.Function.
Require Import FP.Structures.Proxy.
Require Import FP.Relations.Setoid.

Import ProperNotation.

Class EqvEnv :=
  { (* equivalence *)
    env_PER : Type -> Type
  ; env_eqv : forall {T} {p:Px (env_PER T)}, T -> T -> Prop
  ; (* eqv is a partial equivalence relation *)
    env_PER_WF : forall (T:Type) {p:Px (env_PER T)}, Type
  ; env_eqv_WF :>
      forall {T} {p:Px (env_PER T)} {pwf:Px (env_PER_WF T)},
      PER env_eqv
  }.
Arguments env_eqv {EqvEnv T p} _ _ : simpl never.

Class EqvEnvLogical {EqvEnv_:EqvEnv} :=
  { eqv_env_logical_P :>
      forall
        {A} {aP:Px (env_PER A)}
        {B} {bP:Px (env_PER B)},
      Px (env_PER (A -> B))
  ; eqv_env_logical_PE_WF :>
      forall
        {A} {aP:Px (env_PER A)} (aPWF:Px (env_PER_WF A))
        {B} {bP:Px (env_PER B)} (bPWF:Px (env_PER_WF B)),
      Px (env_PER_WF (A -> B))
  ; eqv_env_logical_intro :
      forall
        {A} {aPER:Px (env_PER A)}
        {B} {bPER:Px (env_PER B)}
        {f:A -> B} {g:A -> B},
      (env_eqv ==> env_eqv) f g -> env_eqv f g
  ; eqv_env_logical_elim :
      forall
        {A} {aPER:Px (env_PER A)}
        {B} {bPER:Px (env_PER B)}
        {f:A -> B} {g:A -> B},
      env_eqv f g -> (env_eqv ==> env_eqv) f g
  }.

(*
not sure if this is needed or not
Section EqvEnv.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvLogical_:EqvEnvLogical}.

  Global Instance eqv_env_logical_P' :
    forall
      {P}
      {A} {aP:Px (P A)}
      {B} {bP:Px (P B)}
      (e:P = env_PER),
    Px (P (A -> B)).
  Proof.
    intros.
    rewrite e in *.
    eauto with typeclass_instances.
  Qed.
End EqvEnv.
*)

Section EqvEnvLogical.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvWF_:EqvEnvLogical}.

  Section Proper_Elim.
    Context {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}.
    Context {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}.
    Context {f:A -> B} {fP:Proper env_eqv f}.
    Global Instance Proper_PE_R_elim1 : Proper (env_eqv ==> env_eqv) f :=
      eqv_env_logical_elim fP.

    Context {C} {cER:Px (env_PER C)} {cER':Px (env_PER_WF C)}.
    Context {g:A -> B -> C} {gP:Proper env_eqv g}.
    Global Instance Proper_PE_R_elim2 : Proper (env_eqv ==> env_eqv ==> env_eqv) g.
      unfold Proper,"==>" at 1 ; intros.
      repeat apply eqv_env_logical_elim ; auto.
    Qed.
  End Proper_Elim.

  Section Proper_App.
    Context {A} {aER:Px (env_PER A)} {aER':Px (env_PER_WF A)}.
    Context {B} {bER:Px (env_PER B)} {bER':Px (env_PER_WF B)}.
    Context (x:A) {xP:Proper env_eqv x}.
    Context (f:A -> B) {fP:Proper env_eqv f}.
    Global Instance Proper_PE_R_app : Proper env_eqv (f x) := Proper_PE_R_elim1 x x xP.
  End Proper_App.
End EqvEnvLogical.

Ltac logical_eqv_intro_once :=
  match goal with
  | [ |- ?R ?A ?B ] =>
      match type of A with
      | ?T -> ?U => apply eqv_env_logical_intro ; unfold "==>" at 1 ; intros
      | Fun ?T ?U => apply eqv_env_logical_intro ; unfold "==>" at 1 ; intros
      end
  end.

Ltac logical_eqv_intro := repeat logical_eqv_intro_once.
Ltac logical_eqv_elim_once :=
  match goal with
  | [ |- ?R (?f ?x) (?g ?y) ] => apply eqv_env_logical_elim
  end.
Ltac logical_eqv_elim := repeat logical_eqv_elim_once.

Create HintDb logical_eqv_db.

Ltac logical_eqv_once :=
  match goal with
  | [ |- env_eqv (?f ?x) (?g ?y) ] =>
      let g_type := type of g in
      match type of f with
      | g_type => logical_eqv_elim_once
      end
  | [ |- env_eqv (fun _ => _) _ ] =>
      logical_eqv_intro_once
  | [ |- env_eqv _ (fun _ => _) ] =>
      logical_eqv_intro_once
  end.
Ltac logical_eqv :=
  match goal with
  | [ |- Proper env_eqv ?x ] => unfold Proper
  | _ => idtac
  end ;
  repeat logical_eqv_once ;
  match goal with
  | [ |- env_eqv ?x ?x ] => change (env_eqv x x) with (Proper env_eqv x)
  | _ => idtac
  end ;
  eauto with logical_eqv_db typeclass_instances.
     
Section morph_proper.
  Context {EqvEnv_:EqvEnv}.
  Context {T:Type} {tPER:Px (env_PER T)} {tPER_WF:Px (env_PER_WF T)}.
  Context {x:T} {y:T}.
  Context (fP:env_eqv x y).
  Definition morph_proper_left : Proper env_eqv x.
  Proof.
    unfold Proper.
    transitivity y ; auto.
    symmetry ; auto.
  Qed.
  Definition morph_proper_right : Proper env_eqv y.
  Proof.
    unfold Proper.
    transitivity x ; auto.
    symmetry ; auto.
  Qed.
End morph_proper.
Hint Resolve morph_proper_left : logical_eqv_db.
Hint Resolve morph_proper_right : logical_eqv_db.
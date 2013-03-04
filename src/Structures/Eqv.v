Require Import FP.Data.Function.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.Injection.
Require Import FP.Structures.EqvRel.
Require Import FP.Structures.Proxy.
Require Import FP.Relations.Setoid.

Import FunctionNotation.

Class Eqv T := { eqv : T -> T -> Prop }.
Arguments eqv {T Eqv} _ _ : simpl never.

Definition Eqv_Proxy2 {T} {Eqv_:Eqv T} : Proxy (Eqv T) := {| proxy := Eqv_ |}.
Definition Proxy2_Eqv {T} {Proxy2_:Proxy (Eqv T)} : Eqv T := proxy Proxy2_.
Hint Resolve Eqv_Proxy2 : typeclass_instances.
Hint Immediate Proxy2_Eqv : typeclass_instances.

Section Eqv.
  Context {T} {Eqv_:Eqv T}.

  Definition not_eqv : T -> T -> Prop := not '..' eqv.
End Eqv.

Class EqvWF T {Eqv_:Eqv T} := { eqv_equivalence :> Equivalence eqv }.
Class PEqvWF T {Eqv_:Eqv T} := { peqv_equivalence :> PER eqv }.

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

Definition eqv_EqvEnv : EqvEnv :=
  {| eqv_env_eqv_P := Eqv
  ;  eqv_env_eqv := fun T (Proxy2_:Proxy2 Eqv T) => eqv
  ;  eqv_env_E_PWF := fun T (p:Proxy2 Eqv T) => EqvWF T
  ;  eqv_env_E_WF := fun T (p:Proxy2 Eqv T) (pwf:EqvWF T) => eqv_equivalence
  ;  eqv_env_PE_PWF := fun T (p:Proxy2 Eqv T) => PEqvWF T
  ;  eqv_env_PE_WF := fun T (p:Proxy2 Eqv T) (pwf:PEqvWF T) => peqv_equivalence
  |}.
Instance eqv_E_R {A} {Eqv_:Eqv A} {EqvWF_:EqvWF A} :
    E_R (EqvEnv_:=eqv_EqvEnv) A :=
  { E_R_eqv_P := Eqv_Proxy2
  ; E_R_eqv_PWF := EqvWF_ 
  }.
Instance eqv_PE_R {A} {PEqv_:Eqv A} {PEqvWF_:PEqvWF A} :
    PE_R (EqvEnv_:=eqv_EqvEnv) A :=
  { PE_R_eqv_P := Eqv_Proxy2
  ; PE_R_eqv_PWF := PEqvWF_ 
  }.

Module EqvNotation.
  Infix "~=!" := eqv_dec (at level 35, no associativity).
  Infix "/~=!" := neg_eqv_dec (at level 35, no associativity).

  Infix "~=?" := eqv_dec_p (at level 35, no associativity).
  Infix "/~=?" := neg_eqv_dec_p (at level 35, no associativity).

  Infix "~=" := eqv (at level 70, no associativity).
  Infix "/~=" := not_eqv (at level 70, no associativity).
End EqvNotation.
Import EqvNotation.
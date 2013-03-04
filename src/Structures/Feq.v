Require Import FP.Structures.Proxy.
Require Import FP.Relations.Setoid.
Require Import FP.Structures.EqvEnv.

Import ProperNotation.

Class Feq T :=
  { feq : T -> T -> Prop }.
Definition Feq_Proxy2 {T} {Feq_:Feq T} : Proxy (Feq T) := {| proxy := Feq_ |}.
Definition Proxy2_Feq {T} {Feq_:Proxy (Feq T)} : Feq T := proxy Feq_.
Hint Resolve Feq_Proxy2 : typeclass_instances.
Hint Immediate Proxy2_Feq : typeclass_instances.

Class Feq_E_WF T {Feq_:Feq T} :=
  { feq_E_WF : Equivalence feq }.
Class Feq_PE_WF T {Feq_:Feq T} :=
  { feq_PE_WF : PER feq }.
Class FeqIsEq T {Feq_:Feq T} :=
  { feq_is_eq :  feq = eq }.

Definition feq_EqvEnv : EqvEnv :=
  {| eqv_env_eqv_P := @Feq
  ;  eqv_env_eqv := fun T (p:Proxy2 Feq T) => feq
  ;  eqv_env_E_PWF := fun T (p:Proxy2 Feq T) => Feq_E_WF T
  ;  eqv_env_E_WF := fun T (p:Proxy2 Feq T) (pwf:Feq_E_WF T) => feq_E_WF
  ;  eqv_env_PE_PWF := fun T (p:Proxy2 Feq T) => Feq_PE_WF T
  ;  eqv_env_PE_WF := fun T (p:Proxy2 Feq T) (pwf:Feq_PE_WF T) => feq_PE_WF
  |}.
Section EqvEnvWF.
  Context {EqvEnv_:EqvEnv}.
  Class EqvEnvWF2 :=
    { eqv_env_functional_eqv_P :>
        forall
          {A} {aP:Proxy2 eqv_env_eqv_P A}
          {B} {bP:Proxy2 eqv_env_eqv_P B},
            Proxy2 eqv_env_eqv_P (A -> B)
    ; eqv_env_functional_PE_PWF :
        forall
          {A} {aP:Proxy2 eqv_env_eqv_P A} (aPWF:eqv_env_PE_PWF A)
          {B} {bP:Proxy2 eqv_env_eqv_P B} (bPWF:eqv_env_PE_PWF B),
            eqv_env_PE_PWF (A -> B)
    ; eqv_env_logical_intro :
        forall
          {A} {aPER:Proxy2 eqv_env_eqv_P A}
          {B} {bPER:Proxy2 eqv_env_eqv_P B}
          {f:A -> B} {g:A -> B},
            (eqv_env_eqv ==> eqv_env_eqv) f g -> eqv_env_eqv f g
    ; eqv_env_logical_elim :
        forall
          {A} {aPER:Proxy2 eqv_env_eqv_P A}
          {B} {bPER:Proxy2 eqv_env_eqv_P B}
          {f:A -> B} {g:A -> B},
            eqv_env_eqv f g -> (eqv_env_eqv ==> eqv_env_eqv) f g
    }.
End EqvEnvWF.

Section Fun_Feq.
  Context {A} {aF:Feq A} {B} {bF:Feq B}.
  Global Instance Fun_Feq : Feq (A -> B) | 2 :=
    { feq := (feq ==> feq) }.

  Variable (aPEWF:Feq_PE_WF A) (bPEWF:Feq_PE_WF B).
  Global Instance Fun_Feq_PE_WF : Feq_PE_WF (A -> B) | 2.
  Proof.
    inversion aPEWF ; inversion bPEWF.
    repeat econstructor.
    - unfold Symmetric ; intros.
      simpl in * ; unfold "==>" in * ; intros.
      symmetry.
      apply H.
      symmetry.
      exact H0.
    - unfold Transitive ; intros.
      transitivity y ; simpl in * ; unfold "==>" in * ; intros ; auto.
  Qed.
End Fun_Feq.
Section Univ_Feq.
  Context {A:Type}.
  Global Instance barf : Feq A | 3 :=
    { feq := eq }.
  Global Instance bargl : Feq_PE_WF A | 3.
  Proof.
    repeat econstructor ; simpl ; auto ; unfold Transitive ; intros ; subst ; auto.
  Qed.
End Univ_Feq.

Print HintDb typeclass_instances.
Section Fun_Feq2.
  Global Instance foo : EqvEnvWF2 (EqvEnv_:=feq_EqvEnv).
  Proof.
    econstructor ; intros.
    apply Fun_Feq_PE_WF ; auto.
    simpl ; auto.
    simpl in H ; auto.
  Qed.
End Fun_Feq2.

Instance eq_E_R {A} : E_R (EqvEnv_:=eq_EqvEnv) A :=
  { E_R_eqv_P := {| proxy2 := tt |}
  ; E_R_eqv_PWF := tt
  }.
Instance eq_PE_R {A} : PE_R (EqvEnv_:=eq_EqvEnv) A :=
  { PE_R_eqv_P := {| proxy2 := tt |}
  ; PE_R_eqv_PWF := tt
  }.
                
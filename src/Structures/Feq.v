Require Import FP.Structures.Proxy.
Require Import FP.Relations.Setoid.
Require Import FP.Structures.EqvEnv.

Import ProperNotation.

Class Feq T :=
  { feq : T -> T -> Prop }.
Definition Feq_Px {T} {Feq_:Feq T} : Px (Feq T) := Feq_.
Definition Px_Feq {T} {Px_:Px (Feq T)} : Feq T := Px_.
Hint Resolve Feq_Px : typeclass_instances.
Hint Immediate Px_Feq : typeclass_instances.

Class Feq_E_WF T {Feq_:Feq T} :=
  { feq_E_WF : Equivalence feq }.
Class Feq_PE_WF T {Feq_:Feq T} :=
  { feq_PE_WF : PER feq }.
Definition Feq_PE_WF_Px {T} {Feq_:Feq T} {Feq_PE_WF_:Feq_PE_WF T}
    : Px (Feq_PE_WF T) := Feq_PE_WF_.
Definition Px_Feq_PE_WF {T} {Feq_:Feq T} {Px_:Px (Feq_PE_WF T)}
    : Feq_PE_WF T := Px_.
Hint Resolve Feq_PE_WF_Px : typeclass_instances.
Hint Immediate Px_Feq_PE_WF : typeclass_instances.

Class FeqIsEq T {Feq_:Feq T} :=
  { feq_is_eq :  feq = eq }.

Definition feq_EqvEnv : EqvEnv :=
  {| env_PER := @Feq
  ;  env_eqv := fun T (p:Px (Feq T)) => feq
  ;  env_PER_WF := fun T (p:Px (Feq T)) => Feq_PE_WF T
  ;  env_eqv_WF := fun T (p:Px (Feq T)) (pwf:Px (Feq_PE_WF T)) => feq_PE_WF
  |}.

Section Fun_Feq.
  Context {A} {aF:Feq A} {B} {bF:Feq B}.
  Global Instance Fun_Feq : Feq (A -> B) | 9 :=
    { feq := (feq ==> feq) }.

  Variable (aPEWF:Feq_PE_WF A) (bPEWF:Feq_PE_WF B).
  Global Instance Fun_Feq_PE_WF : Feq_PE_WF (A -> B) | 9.
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
  Local Instance Univ_Feq : Feq A | 10 :=
    { feq := eq }.
  Local Instance Univ_Feq_PE_WF : Feq_PE_WF A | 10.
  Proof.
    repeat econstructor ; simpl ; auto ; unfold Transitive ; intros ; subst ; auto.
  Qed.
End Univ_Feq.

Section Feq_EqvEnvLogical.
  Definition feq_EqvEnvLogical : EqvEnvLogical (EqvEnv_:=feq_EqvEnv).
  Proof.
    econstructor ; intros.
    apply Fun_Feq_PE_WF ; auto.
    simpl ; auto.
    simpl in H ; auto.
  Qed.
End Feq_EqvEnvLogical.
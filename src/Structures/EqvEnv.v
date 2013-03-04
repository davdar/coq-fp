Require Import FP.Structures.Proxy.
Require Import FP.Relations.Setoid.

Import ProperNotation.

Class EqvEnv :=
  { (* equivalence *)
    eqv_env_eqv_P : Type -> Type
  ; eqv_env_eqv : forall {T} {p:Proxy (eqv_env_eqv_P T)}, T -> T -> Prop
  ; (* eqv is a partial equivalence relation *)
    eqv_env_PE_PWF : forall (T:Type) {p:Proxy (eqv_env_eqv_P T)}, Type
  ; eqv_env_PE_WF :
      forall {T} {p:Proxy (eqv_env_eqv_P T)} {pwf:Proxy (eqv_env_PE_PWF T)},
        PER eqv_env_eqv
  }.

Class EqvEnvWF {EqvEnv_:EqvEnv} :=
  { eqv_env_functional_eqv_P :>
      forall
        {A} {aP:Proxy (eqv_env_eqv_P A)}
        {B} {bP:Proxy (eqv_env_eqv_P B)},
          Proxy (eqv_env_eqv_P (A -> B))
  ; eqv_env_functional_PE_PWF :
      forall
        {A} {aP:Proxy (eqv_env_eqv_P A)} (aPWF:Proxy (eqv_env_PE_PWF A))
        {B} {bP:Proxy (eqv_env_eqv_P B)} (bPWF:Proxy (eqv_env_PE_PWF B)),
          Proxy (eqv_env_PE_PWF (A -> B))
  ; eqv_env_logical_intro :
      forall
        {A} {aPER:Proxy (eqv_env_eqv_P A)}
        {B} {bPER:Proxy (eqv_env_eqv_P B)}
        {f:A -> B} {g:A -> B},
          (eqv_env_eqv ==> eqv_env_eqv) f g -> eqv_env_eqv f g
  ; eqv_env_logical_elim :
      forall
        {A} {aPER:Proxy (eqv_env_eqv_P A)}
        {B} {bPER:Proxy (eqv_env_eqv_P B)}
        {f:A -> B} {g:A -> B},
          eqv_env_eqv f g -> (eqv_env_eqv ==> eqv_env_eqv) f g
  }.

Section PE_R.
  Context {EqvEnv_:EqvEnv}.

  Class PE_R (T:Type) : Type :=
    { PE_R_eqv_P :> Proxy (eqv_env_eqv_P T)
    ; PE_R_eqv_PWF : Proxy (eqv_env_PE_PWF T)
    }.

  Context {T} {PE_R_:PE_R T}.
  Definition PE_eqv : T -> T -> Prop := eqv_env_eqv.
  Global Instance PE_R_env_peqv_WF : PER eqv_env_eqv :=
    eqv_env_PE_WF (pwf:=PE_R_eqv_PWF).
End PE_R.

Section EqvEnvWF.
  Context {EqvEnv_:EqvEnv}.
  Context {EqvEnvWF_:EqvEnvWF}.

  Section Fun_PE_R.
    Context {A} {aER:PE_R A}.
    Context {B} {bER:PE_R B}.
    Global Instance EqvEnvWF_Fun_E_R : PE_R (A -> B) :=
      {| PE_R_eqv_P := eqv_env_functional_eqv_P
       ; PE_R_eqv_PWF := eqv_env_functional_PE_PWF PE_R_eqv_PWF PE_R_eqv_PWF
      |}.
  End Fun_PE_R.

  Section Proper_Elim.
    Context {A} {aER:PE_R A}.
    Context {B} {aBR:PE_R B}.
    Context {f:A -> B} {fP:Proper PE_eqv f}.
    Global Instance Proper_PE_R_elim1 : Proper (PE_eqv ==> PE_eqv) f :=
      eqv_env_logical_elim fP.

    Context {C} {cER:PE_R C} {g:A -> B -> C} {gP:Proper PE_eqv g}.
    Global Instance Proper_PE_R_elim2 : Proper (PE_eqv ==> PE_eqv ==> PE_eqv) g.
      unfold Proper,"==>" at 1 ; intros.
      repeat apply eqv_env_logical_elim ; auto.
    Qed.
  End Proper_Elim.

  Section Proper_App.
    Context {A} {aER:PE_R A}.
    Context {B} {aBR:PE_R B}.
    Context {x:A} {xP:Proper PE_eqv x}.
    Context {f:A -> B} {fP:Proper PE_eqv f}.
    Global Instance Proper_PE_R_app : Proper PE_eqv (f x) := Proper_PE_R_elim1 x x xP.
  End Proper_App.
End EqvEnvWF.

Ltac logical_eqv_intro_once :=
  match goal with
  | [ |- ?R ?A ?B ] =>
      match type of A with
      | ?T -> ?U => apply eqv_env_logical_intro ; unfold "==>" at 1 ; intros
      end
  end.
Ltac logical_eqv_intro := repeat logical_eqv_intro_once.
Ltac logical_eqv_elim_once :=
  match goal with
  | [ |- ?R (?f ?x) (?g ?y) ] => apply eqv_env_logical_elim
  end.
Ltac logical_eqv_elim := repeat logical_eqv_elim_once.

Create HintDb logical_eqv_db.
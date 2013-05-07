Require Import FP.Data.String.
Require Import FP.Data.Function.
Require Import FP.Data.Identity.
Require Import FP.Data.Sum.
Require Import FP.Data.Unit.
Require Import FP.Data.SumRelations.
Require Import FP.Structures.Additive.
Require Import FP.Structures.EqvEnv.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Monad.
Require Import FP.Structures.Applicative.
Require Import FP.Structures.Counit.
Require Import FP.Structures.Injection.
Require Import FP.Structures.FUnit.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadError.
Require Import FP.Structures.Proxy.
Require Import FP.Structures.Deriving.
Require Import FP.Structures.FUnit.
Require Import FP.Structures.FUnitDeriving.
Require Import FP.Structures.MonadReader.
Require Import FP.Structures.MonadState.
Require Import FP.Structures.MonadReader.
Require Import FP.Structures.MonadDeriving.
Require Import FP.Structures.MonadTrans.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Ord.
Require Import FP.Relations.RelDec.
Require Import FP.Relations.Setoid.
Require Import FP.Relations.Function.

Import AdditiveNotation.
Import EqvNotation.
Import FunctionNotation.
Import FunctorNotation.
Import MonadNotation.
Import ProperNotation.

Arguments Some {A} _.
Arguments None {A}.

Section sum_Bijection.
  Context {A:Type}.

  Definition option_to_sum (aM:option A) : unit + A :=
    match aM with
    | None => inl tt
    | Some a => inr a
    end.
  Global Instance option_to_sum_InjectionResp_eq
      : InjectionRespect (option A) (unit+A) option_to_sum eq eq.
  Proof.
    constructor ; unfold Proper ; simpl in * ; intros ; try congruence.
    destruct x,y ; simpl in * ; congruence.
  Qed.

  Definition sum_to_option (aM:unit+A) : option A :=
    match aM with
    | inl tt => None
    | inr a => Some a
    end.
  Global Instance sum_to_option_InjectionInverse_eq
      : InjectionInverse (unit+A) (option A) sum_to_option option_to_sum eq.
  Proof.
    constructor ; intros.
    destruct x ; [ destruct u | idtac ] ; simpl in * ; auto.
  Qed.
End sum_Bijection.

Module option_DTKS1_Arg <: DerivingTheKitchenSink1_Arg.
  Definition T A := option A.
  Definition U A := (unit:Type)+A.
  Definition to {A} (x:T A) := option_to_sum x.
  Definition from {A} (x:U A) := sum_to_option x.
  Definition InjResp A : InjectionRespect (T A) (U A) to eq eq := _.
  Definition InjInv A : InjectionInverse (U A) (T A) from to eq := _.
  Definition U_EqDec :
    forall {A} {EqDec_:EqDec A},
    EqDec (U A) := _.
  Definition U_EqDec_RDC :
    forall {A} {EqDec_:EqDec A} {EqDec_RDC:RelDecCorrect A eq eq_dec},
    RelDecCorrect (U A) eq eq_dec := _.
  Definition U_Eqv :
    forall {A} {Eqv_:Eqv A},
    Eqv (U A) := _.
  Definition U_Eqv_PE_WF :
    forall {A} {Eqv_:Eqv A} {Eqv_PE_WF_:Eqv_PE_WF A},
    Eqv_PE_WF (U A) := _.
  Definition U_Eqv_E_WF :
    forall {A} {Eqv_:Eqv A} {Eqv_PE_WF_:Eqv_E_WF A},
    Eqv_E_WF (U A) := _.
  Definition U_EqvDec :
    forall {A} {EqvDec_:EqvDec A},
    EqvDec (U A) := _.
  Definition U_EqvDec_RDC :
    forall {A} {Eqv_:Eqv A} {EqvDec_:EqvDec A} {EqvDec_RDC_:RelDecCorrect A eqv eqv_dec},
    RelDecCorrect (U A) eqv eqv_dec := _.
  Definition U_Ord :
    forall {A} {Ord_:Ord A},
    Ord (U A) := _.
  Definition U_OrdWF :
    forall {A} {Eqv_:Eqv A} {Eqv_E_WF_:Eqv_E_WF A} {Ord_:Ord A} {OrdWF_:OrdWF A},
    OrdWF (U A) := _.
  Definition U_OrdDec :
    forall {A} {OrdDec_:OrdDec A},
    OrdDec (U A) := _.
  Definition U_ODC :
    forall {A} {Eqv_:Eqv A} {Ord_:Ord A} {OrdDec_:OrdDec A} {ODC_:OrdDecCorrect A},
    OrdDecCorrect (U A) := _.
  Definition U_Lattice :
    forall {A} {Lattice_:Lattice A},
    Lattice (U A) := _.
  Definition U_LatticeWF :
    forall {A}
      {Eqv_:Eqv A} {Eqv_E_WF_:Eqv_E_WF A}
      {Ord_:Ord A} {OrdWF_:OrdWF A}
      {Lattice_:Lattice A} {LatticeWF_:LatticeWF A},
    LatticeWF (U A) := _.
  Definition U_BoundedLattice :
    forall {A} {BoundedLattice_:BoundedLattice A},
    BoundedLattice (U A) := _.
  Definition U_BoundedLatticeWF :
    forall {A}
      {Eqv_:Eqv A} {Eqv_E_WF_:Eqv_E_WF A}
      {Ord_:Ord A} {OrdWF_:OrdWF A}
      {Lattice_:Lattice A} {LatticeWF_:LatticeWF A}
      {BoundedLattice_:BoundedLattice A} {BoundedLatticeWF_:BoundedLatticeWF A},
    BoundedLatticeWF (U A) := _.
End option_DTKS1_Arg.

Module option_DTKS1 := DerivingTheKitchenSink1 option_DTKS1_Arg.
Import option_DTKS1.

Instance Some_InjectionRespect_eqv {A} {Eqv_:Eqv A} :
  InjectionRespect A (option A) Some eqv eqv.
Proof.
  constructor ; unfold Proper,"==>","<==" ; intros.
  constructor ; auto.
  inversion H ; auto.
Qed.

Instance None_Proper {A} {Eqv_:Eqv A} :
  Proper eqv (None (A:=A)).
Proof.
  unfold Proper,eqv ; simpl.
  eapply InjectionRespect_eta ; reflexivity.
Qed.

Instance Some_Proper {A} {Eqv_:Eqv A} :
  Proper eqv (Some (A:=A)).
Proof.
  apply eqv_env_logical_intro_eqv.
  apply InjectionRespect_eta.
Qed.

Ltac destruct_option_eqv x y :=
  match goal with
  | [ e : eqv x y |- _ ] =>
      destruct x,y ;
      [ apply InjectionRespect_beta in e
      | inversion e
      | inversion e
      | idtac ]
  end.

Definition option_elim {A C} (aM:option A) (z:C) (f:A -> C) : C :=
  match aM with
  | None => z
  | Some a => f a
  end.

Global Instance option_elim_respect {A C} {aP:Eqv A} {cP:Eqv C} :
  Proper eqv (option_elim (A:=A) (C:=C)).
Proof.
  unfold option_elim.
  logical_eqv_eqv.
  destruct_option_eqv x y ; logical_eqv_eqv.
Qed.

Ltac fold_option_elim :=
  match goal with
  | [ |- context
         [ match ?aM with
           | None => ?z
           | Some a => (@?f a)
           end
         ]
    ] => fold (option_elim aM z f)
  end.

Definition from_option {A} (a:A) (aM:option A) : A :=
  match aM with
  | None => a
  | Some a' => a'
  end.

Section throw_msg_option.
  Context {m E} {mM:Monad m} {mE:MError E m} {eI:HasInjection string E}.

  Definition throw_msg_option {A} (msg:string) (xM:option A) : m A :=
    match xM with
    | None => throw_msg msg
    | Some x => ret x
    end.
End throw_msg_option.

Section monoid_option.
  Context {T} {TM:Monoid T}.
  Definition monoid_option (xM:option T) : T :=
    match xM with
    | None => gunit
    | Some x => x
    end.
End monoid_option.

Section Foldable.
  Context {A:Type}.
  Definition option_cofold {m} {M:Comonad m} {B}
      (f:A -> m B -> B) (b:m B) (aM:option A) : B :=
    match aM with
    | None => counit b
    | Some a => f a b
    end.
  Global Instance option_Foldable : Foldable A (option A) :=
    { cofold := @option_cofold }.
End Foldable.

(* option_t *)

Inductive option_t m (A:Type) := OptionT { un_option_t : m (option A) }.
Arguments OptionT {m A} _.
Arguments un_option_t {m A} _.

Section m_option_Bijection.
  Context {m:Type -> Type} {A:Type}.

  Definition option_t_to_m_option : option_t m A -> m (option A) := un_option_t.
  Global Instance option_t_to_m_option_InjectionResp_eq
      : InjectionRespect (option_t m A) (m (option A)) option_t_to_m_option eq eq.
  Proof.
    constructor ; try congruence.
    unfold Proper,"<==" ; intros.
    destruct x,y ; simpl in * ; congruence.
  Qed.
  Arguments option_t_to_m_option _ /.

  Definition m_option_to_option_t : m (option A) -> option_t m A := OptionT.
  Global Instance m_option__to_option_t_InjectionInverse_eq
      : InjectionInverse (m (option A)) (option_t m A)
                         m_option_to_option_t option_t_to_m_option eq.
  Proof.
    constructor ; auto.
  Qed.
End m_option_Bijection.

Module option_t_DTKS2_Arg <: DerivingTheKitchenSink2_Arg.
  Definition T (m:Type->Type) A := option_t m A.
  Definition U (m:Type->Type) A := m (option A).
  Definition to {m A} (x:T m A) := option_t_to_m_option x.
  Definition from {m A} (x:U m A) := m_option_to_option_t x.
  Definition InjResp m A : InjectionRespect (T m A) (U m A) to eq eq := _.
  Definition InjInv m A : InjectionInverse (U m A) (T m A) from to eq := _.
  Section m.
    Context {m:Type->Type}.
    Definition U_EqDec :
      forall
        {EqDec_m :
           forall {X} {EqDec_:EqDec X},
           EqDec (m X)}
        {A} {EqDec_:EqDec A},
      EqDec (U m A) := _.
    Definition U_EqDec_RDC :
      forall
        {EqDec_m :
           forall {X} {EqDec_:EqDec X},
           EqDec (m X)}
        {EqDec_RDC_m :
           forall {X} {EqDec_:EqDec X} {EqDec_RDC_:RelDecCorrect X eq eq_dec},
           RelDecCorrect (m X) eq eq_dec}
        {A} {EqDec_:EqDec A} {RDC_A:RelDecCorrect A eq eq_dec},
      RelDecCorrect (U m A) eq eq_dec := _.
    Definition U_Eqv :
      forall
        {Eqv_m :
           forall {X} {Eqv_:Eqv X},
           Eqv (m X)}
        {A} {Eqv_:Eqv A},
      Eqv (U m A) := _.
    Definition U_Eqv_PE_WF :
      forall
        {Eqv_m :
           forall {X} {Eqv_:Eqv X},
           Eqv (m X)}
        {Eqv_PE_WF_m :
           forall {X} {Eqv_:Eqv X} {Eqv_PE_WF_:Eqv_PE_WF X},
           Eqv_PE_WF (m X)}
        {A} {Eqv_:Eqv A} {Eqv_PE_WF_:Eqv_PE_WF A},
      Eqv_PE_WF (U m A) := _.
    Definition U_Eqv_E_WF :
      forall
        {Eqv_m :
           forall {X} {Eqv_:Eqv X},
           Eqv (m X)}
        {Eqv_E_WF_m :
           forall {X} {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X},
           Eqv_E_WF (m X)}
        {A} {Eqv_:Eqv A} {Eqv_E_WF_:Eqv_E_WF A},
      Eqv_E_WF (U m A) := _.
    Definition U_EqvDec :
      forall
        {EqvDec_m :
           forall {X} {EqvDec_:EqvDec X},
            EqvDec (m X)}
        {A} {EqvDec_:EqvDec A},
      EqvDec (U m A) := _.
    Definition U_EqvDec_RDC :
      forall
        {Eqv_m :
           forall {X} {Eqv_:Eqv X},
           Eqv (m X)}
        {EqvDec_m :
           forall {X} {EqvDec_:EqvDec X},
           EqvDec (m X)}
        {EqvDec_RDC_m :
           forall
             {X} {Eqv_:Eqv X} {EqvDec_:EqvDec X}
             {RDC_A:RelDecCorrect X eqv eqv_dec},
           RelDecCorrect (m X) eqv eqv_dec}
        {A} {Eqv_:Eqv A} {EqvDec_:EqvDec A} {RDC_A:RelDecCorrect A eqv eqv_dec},
      RelDecCorrect (U m A) eqv eqv_dec := _.
    Definition U_Ord :
      forall
        {Ord_m :
           forall {X} {Ord_:Ord X},
           Ord (m X)}
        {A} {Ord_:Ord A},
      Ord (U m A) := _.
    Definition U_OrdWF :
      forall
        {Eqv_m :
           forall {X} {Eqv_:Eqv X},
           Eqv (m X)}
        {Eqv_E_WF_m :
           forall {X} {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X},
           Eqv_E_WF (m X)}
        {Ord_m :
           forall {X} {Ord_:Ord X},
           Ord (m X)}
        {OrdWF_m :
           forall
             {X}
             {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X}
             {Ord_:Ord X} {Ord_WF_:OrdWF X},
           OrdWF (m X)}
        {A}
        {Eqv_:Eqv A} {Eqv_E_WF_:Eqv_E_WF A}
        {Ord_:Ord A} {Ord_WF_:OrdWF A},
      OrdWF (U m A) := _.
    Definition U_OrdDec :
      forall
        {OrdDec_m :
           forall {X} {OrdDec_:OrdDec X},
           OrdDec (m X)}
        {A} {OrdDec_:OrdDec A},
      OrdDec (U m A) := _.
    Definition U_ODC :
      forall
        {Eqv_m :
           forall {X} {Eqv_:Eqv X},
           Eqv (m X)}
        {Ord_m :
           forall {X} {Ord_:Ord X},
           Ord (m X)}
        {OrdDec_m :
           forall {X} {OrdDec_:OrdDec X},
           OrdDec (m X)}
        {ODC_m :
           forall
             {X} {Eqv_:Eqv X}
             {Ord_:Ord X} {OrdDec_:OrdDec X} {ODC_A:OrdDecCorrect X},
           OrdDecCorrect (m X)}
        {A}
        {Eqv_:Eqv A}
        {Ord_:Ord A} {OrdDec_:OrdDec A} {ODC_A:OrdDecCorrect A},
      OrdDecCorrect (U m A) := _.
    Definition U_Lattice :
      forall
        {Lattice_m :
           forall {X} {Lattice_:Lattice X},
           Lattice (m X)}
        {A} {Lattice_:Lattice A},
      Lattice (U m A) := _.
    Definition U_LatticeWF :
      forall
        {Eqv_m :
           forall {X} {Eqv_:Eqv X},
           Eqv (m X)}
        {Eqv_E_WF_m :
           forall {X} {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X},
           Eqv_E_WF (m X)}
        {Ord_m :
           forall {X} {Ord_:Ord X},
           Ord (m X)}
        {OrdWF_m :
           forall
             {X}
             {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X}
             {Ord_:Ord X} {Ord_WF_:OrdWF X},
           OrdWF (m X)}
        {Lattice_m :
           forall {X} {Lattice_:Lattice X},
           Lattice (m X)}
        {LatticeWF_m :
           forall {X}
             {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X}
             {Ord_:Ord X} {OrdWF_:OrdWF X}
             {Lattice_:Lattice X} {LatticeWF_:LatticeWF X},
           LatticeWF (m X)}
        {A}
        {Eqv_:Eqv A} {Eqv_E_WF_:Eqv_E_WF A}
        {Ord_:Ord A} {OrdWF_:OrdWF A}
        {Lattice_:Lattice A} {LatticeWF_:LatticeWF A},
      LatticeWF (U m A) := _.
    Definition U_BoundedLattice :
      forall 
        {BoundedLattice_m :
           forall {X} {BoundedLattice_:BoundedLattice X},
           BoundedLattice (m X)}
        {A} {BoundedLattice_:BoundedLattice A},
      BoundedLattice (U m A) := _.
    Definition U_BoundedLatticeWF :
      forall
        {Eqv_m :
           forall {X} {Eqv_:Eqv X},
           Eqv (m X)}
        {Eqv_E_WF_m :
           forall {X} {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X},
           Eqv_E_WF (m X)}
        {Ord_m :
           forall {X} {Ord_:Ord X},
           Ord (m X)}
        {OrdWF_m :
           forall
             {X}
             {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X}
             {Ord_:Ord X} {Ord_WF_:OrdWF X},
           OrdWF (m X)}
        {Lattice_m :
           forall {X} {Lattice_:Lattice X},
           Lattice (m X)}
        {LatticeWF_m :
           forall {X}
             {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X}
             {Ord_:Ord X} {OrdWF_:OrdWF X}
             {Lattice_:Lattice X} {LatticeWF_:LatticeWF X},
           LatticeWF (m X)}
        {BoundedLattice_m :
           forall {X} {BoundedLattice_:BoundedLattice X},
           BoundedLattice (m X)}
        {BoundedLatticeWF_m :
           forall {X}
             {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X}
             {Ord_:Ord X} {OrdWF_:OrdWF X}
             {Lattice_:Lattice X} {LatticeWF_:LatticeWF X}
             {BoundedLattice_:BoundedLattice X} {BoundedLatticeWF_:BoundedLatticeWF X},
           BoundedLatticeWF (m X)}
        {A}
        {Eqv_:Eqv A} {Eqv_E_WF_:Eqv_E_WF A}
        {Ord_:Ord A} {OrdWF_:OrdWF A}
        {Lattice_:Lattice A} {LatticeWF_:LatticeWF A}
        {BoundedLattice_:BoundedLattice A} {BoundedLatticeWF_:BoundedLatticeWF A},
      BoundedLatticeWF (U m A) := _.
  End m.
End option_t_DTKS2_Arg.

Module option_DTKS2 := DerivingTheKitchenSink2 option_t_DTKS2_Arg.
Import option_DTKS2.

Section MonadTrans.
  Definition option_t_lift {m} {M:Monad m} {A} : m A -> option_t m A :=
    OptionT '.' bind_fmap Some.
  Global Instance option_t_MonadTrans : MonadTrans option_t :=
    { lift := @option_t_lift }.
End MonadTrans.

Section option_t_Monad.
  Context {m} {FUnit_:FUnit m} {MBind_:MBind m}.

  Definition run_option_t {A} : option_t m A -> m (option A) := un_option_t.

  Section Monad.
    Definition option_t_funit {A} (a:A) : option_t m A := OptionT $ ret $ Some a.
    Global Instance option_t_FUnit : FUnit (option_t m) :=
      { funit := @option_t_funit }.

    Definition option_t_bind {A B}
        (aMM:option_t m A) (f:A -> option_t m B) : option_t m B :=
      OptionT $ begin
        a <- un_option_t aMM ;;
        match a with
        | None => ret None
        | Some a => un_option_t $ f a
        end
      end.
    Global Instance option_t_MBind : MBind (option_t m) :=
      { bind := @option_t_bind }.
  End Monad.

  Global Instance option_t_FApply : FApply (option_t m) := Deriving_FApply_MBind.
  Global Instance option_t_FMap : FMap (option_t m) := Deriving_FMap_FApply.

  Section MonadWF.
    Local Instance EqvEnv_ : EqvEnv := eqv_EqvEnv.
    Local Instance EqvEnvLogical_ : EqvEnvLogical := eqv_EqvEnvLogical.
    Context {PE_R_m:forall {X} {aPER:Eqv X}, Eqv (m X)}.
    Context {PE_R_m': forall {X} {aPER:Eqv X} {blah:Eqv_PE_WF X}, Eqv_PE_WF (m X)}.

    Global Instance OptionT_respect {A} {aP:Eqv A} :
      Proper eqv (OptionT (m:=m) (A:=A)).
    Proof.
      unfold Proper ; logical_eqv_intro_eqv ; auto.
    Qed.

    Global Instance un_option_t_respect {A} {aP:Eqv A} :
      Proper eqv (un_option_t (m:=m) (A:=A)).
    Proof.
      unfold un_option_t ; simpl.
      logical_eqv_eqv.
    Qed.

    Context {FUnitWF_:FUnitWF m}.

    Global Instance option_t_FUnitWF : FUnitWF (option_t m).
    Proof.
      constructor ; intros.
      unfold Proper,env_eqv,funit ; simpl.
      logical_eqv_intro_eqv.
      unfold eqv ; simpl ; logical_eqv_eqv.
    Qed.
    
    Context {MonadWF_:MonadWF m}.

    Global Instance option_t_MonadWF : MonadWF (option_t m).
    Proof.
      Local Ltac my_logical_eqv :=
        repeat (try fold_option_elim ; logical_eqv_eqv).
      constructor ; intros ;
      unfold Proper,">>=",env_eqv ; simpl ; unfold "~=" ; simpl ;
      unfold option_t_to_m_option.
      - rewrite bind_left_unit_eqv ; my_logical_eqv.
      - transitivity (un_option_t aM >>= funit) ; my_logical_eqv.
        + destruct_option_eqv x y ; simpl ; my_logical_eqv.
        + rewrite bind_right_unit_eqv ; my_logical_eqv.
      - rewrite bind_associativity_eqv ; my_logical_eqv.
        destruct_option_eqv x y ; simpl ; my_logical_eqv.
        rewrite bind_left_unit_eqv ; my_logical_eqv.
      - change (let (eqv) := Px_Eqv in eqv)
        with (eqv (T:=option_t m A -> (A -> option_t m B) -> option_t m B)).
        unfold option_t_bind ; my_logical_eqv.
    Qed.

    Global Instance option_t_MonadRespApplicative : MonadRespApplicative (option_t m).
    Proof.
      constructor ; intros.
      change fapply with (bind_fapply (A:=A) (B:=B)).
      logical_eqv.
      assert (Proper env_eqv (bind_fapply (m:=option_t m) (A:=A) (B:=B))).
      pose (bind_fapply_respect (m:=option_t m) (A:=A) (B:=B)).
      Set Printing All.
      Show.
      simpl in p.
      apply p.
      Unset Printing All.
      Show.
      logical_eqv.
      logical_eqv.
      assert (P
  End MonadWF.

    Proof.
      constructor ; intros.
      change fapply with (bind_fapply (A:=A) (B:=B)).
      eapply Proper_PE_R_app.
      logical_eqv.
      eapply bind_fapply_respect.
      change env_eqv with (eqv (T:=option_t m B)).
      logical_eqv_eqv.
      eauto with typeclass_instances.
      unfold bind_fapply.
      logical_eqv.
      unfold fapply. unfold option_t_FApply. unfold Deriving_FApply_MBind.
      unfold deriving_FApply_MBind.
      logical_eqv_eqv.
      reflexivity.

    Global Instance option_t_ApplicativeWF : ApplicativeWF (option_t m) :=
        Deriving_ApplicativeWF_MonadWF.
  End ApplicativeWF.


  Section FPlus.
    Definition option_t_mzero {A} : option_t m A := OptionT $ ret None.
    Definition option_t_mplus {A} {B}
        (aMM:option_t m A) (bMM:option_t m B) : option_t m (A+B) :=
      OptionT $ begin
        a <- un_option_t aMM ;;
        match a with
        | None => un_option_t $ inr <$> bMM
        | Some x => un_option_t $ inl <$> aMM
        end
      end.

    Global Instance option_t_MonadPlus : MonadPlus (option_t m) :=
      { mzero := @option_t_mzero
      ; mplus := @option_t_mplus
      }.
  End FPlus.

  Section MonadError.
    Context {E} {ME:MonadError E m}.

    Definition option_t_throw {A} : E -> option_t m A := lift '.' throw.
    Definition option_t_catch {A}
        (aMM:option_t m A) : (E -> option_t m A) -> option_t m A :=
      OptionT '.' catch (un_option_t aMM) '.' compose un_option_t.
    Global Instance option_t_MonadError : MonadError E (option_t m) :=
      { throw := @option_t_throw
      ; catch := @option_t_catch
      }.
  End MonadError.
*)

  Section MonadReader.
    Context {R} {MR:MReader R m}.

    Definition option_t_ask : option_t m R := lift ask.
    Definition option_t_local {A} (f:R -> R) : option_t m A -> option_t m A :=
      OptionT '.' local f '.' un_option_t.
    Global Instance option_t_MonadReader : MReader R (option_t m) :=
      { ask := option_t_ask
      ; local := @option_t_local
      }.
  End MonadReader.

  Section MonadState.
    Context {S} {MS:MonadState S m}.

    Definition option_t_get : option_t m S := lift get.
    Definition option_t_put (s:S) : option_t m unit := lift $ put s.
    Global Instance option_t_MonadState : MonadState S (option_t m) :=
      { get := option_t_get
      ; put := option_t_put
      }.
  End MonadState.
End option_t_Monad.

Instance option_option_t_HasFunctorInjection
    : HasFunctorInjection option (option_t identity) :=
  { finject := fun _ => OptionT '.' Identity}.
Instance option_t_option_HasFunctorInjection
    : HasFunctorInjection (option_t identity) option :=
  { finject := fun _ => un_identity '.' un_option_t }.

Instance option_FUnit : FUnit option := Deriving_FUnit (option_t identity).
Instance option_MBind : MBind option := Deriving_MBind (option_t identity).
Instance option_FPlus : FPlus option := Deriving_FPlus (option_t identity).

(*
Section MonadPlus_passthrough.
  Context {m} {M:Monad m} {MP:MonadPlus m}.

  Definition option_t_mzero_passthrough {A} : option_t m A := OptionT $ mzero.
  Definition option_t_mplus_passthrough {A B}
      (aMM:option_t m A) (bMM:option_t m B) : option_t m (A+B) :=
    OptionT $ begin
      aMbM <- un_option_t aMM <+> un_option_t bMM ;;
      ret $
        match aMbM with
        | inl aM => inl <$> aM
        | inr bM => inr <$> bM
        end
    end.
  Definition option_t_MonadPlus_passthrough : MonadPlus (option_t m) :=
    {| mzero := @option_t_mzero_passthrough
     ; mplus := @option_t_mplus_passthrough
    |}.
End MonadPlus_passthrough.

*)
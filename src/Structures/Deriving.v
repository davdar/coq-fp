Require Import FP.Data.Function.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Ord.
Require Import FP.Structures.EqvEnv.
Require Import FP.Relations.Setoid.

Import FunctionNotation.
Import ProperNotation.

Section DerivingRelDec.
  Context {T:Type} {U:Type}.
  Variable (inj:T -> U).
  Variable (TR:T -> T -> Prop) (TD:T -> T -> bool).
  Variable (UR:U -> U -> Prop) (UD:U -> U -> bool).
  Context {InjResp:InjectionRespect T U inj TR UR}.
  Context {RDC:RelDecCorrect U UR UD}.
  Variable (poofD:TD = (UD `on` inj)).

  Definition DerivingRelDec : RelDecCorrect T TR TD.
  Proof. constructor ; intros.
    rewrite poofD ; simpl.
      apply InjectionRespect_eta in H.
      apply rel_correct ; auto.
    rewrite poofD in H ; simpl in H.
      apply InjectionRespect_beta.
      apply dec_correct ; auto.
  Qed.
End DerivingRelDec.

Section DerivingInjResp.
  Context {T:Type} {U:Type}.
  Variable (inj:T -> U).
  Variable (TR:T -> T -> Prop) (UR:U -> U -> Prop).
  Variable (poof:TR = (UR `on` inj)).

  Definition DerivingInjResp : InjectionRespect T U inj TR UR.
  Proof. constructor ; unfold Proper,"==>","<==" ; simpl ; intros.
    rewrite poof in H ; auto.
    rewrite poof ; unfold on ; simpl ; auto.
  Qed.
End DerivingInjResp.

Section DerivingInjResp_inv.
  Context {T:Type} {U:Type}.
  Variable (to:T -> U).
  Variable (from:U -> T).
  Variable (TR:T -> T -> Prop) (UR:U -> U -> Prop).
  Context {PER_TR:PER TR}.
  Context {InjResp2:InjectionRespect U T from UR TR}.
  Context {InjInv:InjectionInverse T U to from eq}.
  Variable (poof:UR = (TR `on` from)).

  Definition DerivingInjResp_inv : InjectionRespect T U to TR UR.
  Proof. constructor ; unfold Proper,"==>","<==" ; simpl ; intros.
    rewrite poof ; simpl.
      repeat erewrite <- InjectionInverse_inv ; auto.
    rewrite poof in H ; simpl in H.
      repeat erewrite <- InjectionInverse_inv in H ; auto.
  Qed.
End DerivingInjResp_inv.

Section DerivingInjectionInverse_ext.
  Context {T:Type}.
  Context {U:Type}.
  Variable (to:T->U) (from:U->T).
  Variable (R1:T->T->Prop) (R2:T->T->Prop).
  Context {Refl1:Reflexive R1}.
  Context {Refl2:Reflexive R2}.
  Context {InjInv:InjectionInverse T U to from R1}.
  Context {Pr:Proper (R1 ==> R1 ==> impl) R2}.

  Definition DerivingInjectionInverse_ext : InjectionInverse T U to from R2.
  Proof. constructor ; intros.
    eapply Pr.
    reflexivity.
    apply InjectionInverse_inv.
    reflexivity.
  Qed.
End DerivingInjectionInverse_ext.

Section DerivingInjectionDistribute.
  Context {T:Type}.
  Context {U:Type}.
  Variable (to:T->U) (from:U->T).
  Variable (TM:T->T->T) (UM:U->U->U).
  Variable (eqv:U->U->Prop).
  Context {Eqv:Equivalence eqv}.
  Context {InjInv:InjectionInverse U T from to eqv}.
  Variable (poof:TM = (from '..' (UM `on` to))).

  Definition DerivingInjectionDistribute : InjectionDistribute T U to TM UM eqv.
  Proof. constructor ; intros.
    rewrite poof ; simpl.
    rewrite <- InjectionInverse_inv.
    reflexivity.
  Qed.
End DerivingInjectionDistribute.

Section DerivingInjectionDistribute_ext.
  Context {T:Type}.
  Context {U:Type}.
  Variable (to:T->U).
  Variable (TM:T->T->T) (UM:U->U->U).
  Variable (eqv1:U->U->Prop) (eqv2:U->U->Prop).
  Context {Eqv1:Equivalence eqv1} {Refl2:Reflexive eqv2}.
  Context {InjDist:InjectionDistribute T U to TM UM eqv1}.
  Context {P:Proper (eqv1 ==> eqv1 ==> impl) eqv2}.

  Definition DerivingInjectionDistribute_ext : InjectionDistribute T U to TM UM eqv2.
  Proof.
    constructor ; intros.
    rewrite InjectionDistribute_law.
    reflexivity.
  Qed.
End DerivingInjectionDistribute_ext.

Section DerivingEqRDC.
  Context {T} {EqDec_T:EqDec T}.
  Context {U} {EqDec_U:EqDec U} {RDC_U:RelDecCorrect U eq eq_dec}.
  Variable (inj:T -> U).
  Context {InjResp:InjectionRespect T U inj eq eq}.
  Variable (poof:(eq_dec (T:=T)) = (eq_dec `on` inj)).

  Definition DerivingEqRDC : RelDecCorrect T eq eq_dec.
  Proof.
    repeat (constructor ; simpl in * ; intros).
    rewrite poof ; simpl.
      apply rel_correct.
      apply InjectionRespect_eta ; auto.
    rewrite poof in H ; simpl in H.
      apply dec_correct in H.
      apply InjectionRespect_beta ; auto.
    Qed.
End DerivingEqRDC.

Section DerivingEqv_PE_WF.
  Context {T} {T_Eqv:Eqv T} {U} {U_Eqv:Eqv U} {U_EqvWF:Eqv_PE_WF U}.
  Variable (inj:T -> U).
  Context {T_U_InjResp:InjectionRespect T U inj eqv eqv}.

  Definition DerivingEqv_PE_WF : Eqv_PE_WF T.
  Proof.
    repeat constructor.
    unfold Symmetric ; intros.
      apply InjectionRespect_beta ; apply InjectionRespect_eta in H ; symmetry ; auto.
    unfold Transitive ; intros x y z H1 H2.
      apply InjectionRespect_beta.
      apply InjectionRespect_eta in H1 ; apply InjectionRespect_eta in H2.
      transitivity (inj y) ; auto.
  Qed.
End DerivingEqv_PE_WF.

Section DerivingEqv_E_WF.
  Context {T} {T_Eqv:Eqv T} {U} {U_Eqv:Eqv U} {U_EqvWF:Eqv_E_WF U}.
  Variable (inj:T -> U).
  Context {T_U_InjResp:InjectionRespect T U inj eqv eqv}.

  Definition DerivingEqv_E_WF : Eqv_E_WF T.
  Proof.
    repeat constructor.
    unfold Reflexive ; intros.
      apply InjectionRespect_beta ; reflexivity.
    unfold Symmetric ; intros.
      apply InjectionRespect_beta ; apply InjectionRespect_eta in H ; symmetry ; auto.
    unfold Transitive ; intros x y z H1 H2.
      apply InjectionRespect_beta.
      apply InjectionRespect_eta in H1 ; apply InjectionRespect_eta in H2.
      transitivity (inj y) ; auto.
  Qed.
End DerivingEqv_E_WF.

Section DerivingOrdWF.
  Context {T} {T_Eqv:Eqv T} {T_EqvWF:Eqv_E_WF T} {T_Ord:Ord T}.
  Context {U} {U_Eqv:Eqv U} {U_EqvWF:Eqv_E_WF U} {U_Ord:Ord U} {U_OrdWF:OrdWF U}.
  Variable (inj:T -> U).
  Context {InjResp_eqv:InjectionRespect T U inj eqv eqv}.
  Context {InjResp_lt:InjectionRespect T U inj lt lt}.

  Definition DerivingOrdWF : OrdWF T.
  Proof. constructor.
    unfold Irreflexive, Reflexive, complement ; intros.
      apply InjectionRespect_eta in H.
      apply (irreflexivity H).
    unfold Transitive ; intros.
      apply InjectionRespect_eta in H ; apply InjectionRespect_eta in H0.
      apply InjectionRespect_beta ; transitivity (inj y) ; auto.
    unfold Proper,"==>" ; simpl ; intros.
      apply InjectionRespect_eta in H1.
      apply InjectionRespect_eta in H0.
      apply InjectionRespect_eta in H.
      rewrite H in H1.
      rewrite H0 in H1.
      apply InjectionRespect_beta ; auto.
  Qed.
End DerivingOrdWF.

Section DerivingOrdDecCorrect.
  Context {T} {T_Eqv:Eqv T} {T_Ord:Ord T} {T_OrdDec:OrdDec T}.
  Context {U} {U_Eqv:Eqv U} {U_Ord:Ord U} {U_OrdDec:OrdDec U} {ODC:OrdDecCorrect U}.
  Variable (inj:T -> U).
  Context {InjResp_eqv:InjectionRespect T U inj eqv eqv}.
  Context {InjResp_lt:InjectionRespect T U inj lt lt}.
  Variable (poofD:ord_dec (T:=T) = (ord_dec (T:=U) `on` inj)).

  Definition DerivingOrdDecCorrect : OrdDecCorrect T.
  Proof. constructor ; intros ;
      try rewrite poofD ;
      try rewrite poofD in H ;
      simpl in *.
    apply InjectionRespect_eta in H.
      apply ord_rel_correct_eqv ; auto.
    apply InjectionRespect_eta in H.
      apply ord_rel_correct_lt ; auto.
    apply InjectionRespect_eta in H.
      apply ord_rel_correct_gt ; auto.
    apply InjectionRespect_beta.
      apply ord_dec_correct_eqv ; auto.
    apply InjectionRespect_beta.
      apply ord_dec_correct_lt ; auto.
    apply InjectionRespect_beta.
      apply ord_dec_correct_gt ; auto.
  Qed.
End DerivingOrdDecCorrect.

Section DerivingLatticeWF.
  Context {T:Type}.
  Context {T_Eqv:Eqv T} {T_EqvWF:Eqv_E_WF T}.
  Context {T_Ord:Ord T} {T_OrdWF:OrdWF T}.
  Context {T_Lattice:Lattice T}.
  Context {U:Type}.
  Context {U_Eqv:Eqv U} {U_EqvWF:Eqv_E_WF U}.
  Context {U_Ord:Ord U} {U_OrdWF:OrdWF U}.
  Context {U_Lattice:Lattice U} {U_LatticeWF:LatticeWF U}.
  Variable (inj:T -> U).
  Context {IR_eqv:InjectionRespect T U inj eqv eqv}.
  Context {IR_lt:InjectionRespect T U inj lt lt}.
  Context {ID_meet:InjectionDistribute T U inj lmeet lmeet eqv}.
  Context {ID_join:InjectionDistribute T U inj ljoin ljoin eqv}.

  Definition DerivingLatticeWF : LatticeWF T.
  Proof. constructor ; intros ; constructor ;
      apply InjectionRespect_beta ; rewrite InjectionDistribute_law.
    apply lmeet_ineq.
    apply lmeet_ineq.
    apply ljoin_ineq.
    apply ljoin_ineq.
  Qed.
End DerivingLatticeWF.

Section DerivingBoundedLatticeWF.
  Context {T:Type}.
  Context {T_Eqv:Eqv T} {T_EqvWF:Eqv_E_WF T}.
  Context {T_Ord:Ord T} {T_OrdWF:OrdWF T}.
  Context {T_Lattice:Lattice T}.
  Context {T_BoundedLattice:BoundedLattice T}.
  Context {U:Type}.
  Context {U_Eqv:Eqv U} {U_EqvWF:Eqv_E_WF U}.
  Context {U_Ord:Ord U} {U_OrdWF:OrdWF U}.
  Context {U_Lattice:Lattice U}.
  Context {U_BoundedLattice:BoundedLattice U} {U_BoundedLatticeWF:BoundedLatticeWF U}.
  Variable (to:T->U) (from:U->T).
  Context {InjResp_eqv:InjectionRespect T U to eqv eqv}.
  Context {InjResp_lt:InjectionRespect T U to lt lt}.
  Context {InjInv2:InjectionInverse U T from to eqv}.
  Variable (poof_top:ltop = (from ltop)).
  Variable (poof_bot:lbot = (from lbot)).

  Definition DerivingBoundedLatticeWF : BoundedLatticeWF T.
  Proof. constructor ; intros.
    rewrite poof_top.
      eapply InjectionRespect_beta.
      rewrite <- InjectionInverse_inv.
      apply ltop_ineq.
    rewrite poof_bot.
      eapply InjectionRespect_beta.
      rewrite <- InjectionInverse_inv.
      apply lbot_ineq.
  Qed.
End DerivingBoundedLatticeWF.

Module Type DerivingTheKitchenSink1_Arg.
  Parameter T : Type -> Type.
  Parameter U : Type -> Type.
  Parameter to : forall {A}, T A -> U A.
  Parameter from : forall {A}, U A -> T A.
  Parameter InjResp : forall {A}, InjectionRespect (T A) (U A) to eq eq.
  Parameter InjInv : forall {A}, InjectionInverse (U A) (T A) from to eq.
  Global Declare Instance U_EqDec :
    forall {A} {EqDec_:EqDec A},
    EqDec (U A).
  Global Declare Instance U_EqDec_RDC :
    forall {A} {EqDec_:EqDec A} {RDC_A:RelDecCorrect A eq eq_dec},
    RelDecCorrect (U A) eq eq_dec.
  Global Declare Instance U_Eqv :
    forall {A} {Eqv_:Eqv A},
    Eqv (U A).
  Global Declare Instance U_Eqv_PE_WF :
    forall {A} {Eqv_:Eqv A} {Eqv_PE_WF_:Eqv_PE_WF A},
    Eqv_PE_WF (U A).
  Global Declare Instance U_Eqv_E_WF :
    forall {A} {Eqv_:Eqv A} {Eqv_E_WF_:Eqv_E_WF A},
    Eqv_E_WF (U A).
  Global Declare Instance U_EqvDec :
    forall {A} {EqvDec_:EqvDec A},
    EqvDec (U A).
  Global Declare Instance U_EqvDec_RDC :
    forall {A} {Eqv_:Eqv A} {EqvDec_:EqvDec A} {RDC_A:RelDecCorrect A eqv eqv_dec},
    RelDecCorrect (U A) eqv eqv_dec.
  Global Declare Instance U_Ord :
    forall {A} {Ord_:Ord A},
    Ord (U A).
  Global Declare Instance U_OrdWF :
    forall {A}
      {Eqv_:Eqv A} {Eqv_E_WF_:Eqv_E_WF A}
      {Ord_:Ord A} {Ord_WF_:OrdWF A},
    OrdWF (U A).
  Global Declare Instance U_OrdDec :
    forall {A} {OrdDec_:OrdDec A},
    OrdDec (U A).
  Global Declare Instance U_ODC :
    forall {A}
        {Eqv_:Eqv A}
        {Ord_:Ord A} {OrdDec_:OrdDec A} {ODC_A:OrdDecCorrect A},
    OrdDecCorrect (U A).
  Global Declare Instance U_Lattice :
    forall {A} {Lattice_:Lattice A},
    Lattice (U A).
  Global Declare Instance U_LatticeWF :
    forall {A}
      {Eqv_:Eqv A} {Eqv_E_WF_:Eqv_E_WF A}
      {Ord_:Ord A} {OrdWF_:OrdWF A}
      {Lattice_:Lattice A} {LatticeWF_:LatticeWF A},
    LatticeWF (U A).
  Global Declare Instance U_BoundedLattice :
    forall {A} {BoundedLattice_:BoundedLattice A},
    BoundedLattice (U A).
  Global Declare Instance U_BoundedLatticeWF :
    forall {A}
      {Eqv_:Eqv A} {Eqv_E_WF_:Eqv_E_WF A}
      {Ord_:Ord A} {OrdWF_:OrdWF A}
      {Lattice_:Lattice A} {LatticeWF_:LatticeWF A}
      {BoundedLattice_:BoundedLattice A} {BoundedLatticeWF_:BoundedLatticeWF A},
    BoundedLatticeWF (U A).
End DerivingTheKitchenSink1_Arg.

Module DerivingTheKitchenSink1 (X:DerivingTheKitchenSink1_Arg).
  Import X.
  Arguments T _ /.
  Arguments U _ /.
  Arguments to {A} _ /.
  Arguments from {A} _ /.

  Section Context.
    Context {A:Type}.

    Section EqDec.
      Context {EqDec_:EqDec A} {EqDec_RDC_:RelDecCorrect A eq eq_dec}.

      Global Instance DTKS_EqDec : EqDec (T A) := { eq_dec := eq_dec `on` to }.
      Global Instance DTKS_EqDec_RDC : RelDecCorrect (T A) eq eq_dec :=
        DerivingEqRDC to eq_refl.
    End EqDec.

    Section Eqv.
      Context {Eqv_:Eqv A}.

      Global Instance DTKS_Eqv : Eqv (T A) := { eqv := eqv `on` to }.
      Global Instance DTKS_InjectionRespect_to_eqv
          : InjectionRespect (T A) (U A) to eqv eqv :=
        DerivingInjResp to eqv eqv eq_refl.
    End Eqv.

    Section Eqv_PE_WF.
      Context {Eqv_:Eqv A} {Eqv_PE_WF_:Eqv_PE_WF A}.

      Global Instance DTKS_Eqv_PE_WF : Eqv_PE_WF (T A) :=
        DerivingEqv_PE_WF to.
      Global Instance DTKS_PE_InjectionRespect_from_eqv
          : InjectionRespect (U A) (T A) from eqv eqv :=
        DerivingInjResp_inv from to eqv eqv eq_refl.
    End Eqv_PE_WF.

    Section Eqv_E_WF.
      Context {Eqv_:Eqv A} {Eqv_E_WF_:Eqv_E_WF A}.

      Global Instance DTKS_Eqv_E_WF : Eqv_E_WF (T A) :=
        DerivingEqv_E_WF to.
      Global Instance DTKS_E_InjectionRespect_from_eqv
          : InjectionRespect (U A) (T A) from eqv eqv :=
        DerivingInjResp_inv from to eqv eqv eq_refl.
      Global Instance DTKS_InjectionInverse_from_eqv
          : InjectionInverse (U A) (T A) from to eqv :=
        DerivingInjectionInverse_ext from to eq eqv.
    End Eqv_E_WF.

    Section EqvDec.
      Context {Eqv_:Eqv A} {EqvDec_:EqvDec A} {EqvDec_RDC_:RelDecCorrect A eqv eqv_dec}.

      Global Instance DTKS_EqvDec : EqvDec (T A) := { eqv_dec := eqv_dec `on` to }.
      Global Instance DTKS_EqvDec_RDC : RelDecCorrect (T A) eqv eqv_dec :=
        DerivingRelDec to eqv eqv_dec eqv eqv_dec eq_refl.
    End EqvDec.

    Section Ord.
      Context {Eqv_:Eqv A} {Eqv_PE_WF_:Eqv_E_WF A} {Ord_:Ord A} {OrdWF_:OrdWF A}.
      Context {OrdDec_:OrdDec A} {ODC_:OrdDecCorrect A}.

      Global Instance DTKS_Ord : Ord (T A) := { lt := lt `on` to }.
      Global Instance DTKS_InjectionRespect_to_lt
          : InjectionRespect (T A) (U A) to lt lt :=
        DerivingInjResp to lt lt eq_refl.
      Global Instance DTKS_InjectionRespect_from_lt
          : InjectionRespect (U A) (T A) from lt lt :=
        DerivingInjResp_inv from to lt lt eq_refl.
      Global Instance DTKS_OrdWF : OrdWF (T A) :=
        DerivingOrdWF to.

      Global Instance DTKS_OrdDec : OrdDec (T A) := { ord_dec := ord_dec `on` to }.
      Global Instance DTKS_ODC : OrdDecCorrect (T A) :=
        DerivingOrdDecCorrect to eq_refl.
    End Ord.

    Section Lattice.
      Context {Eqv_:Eqv A} {EqvWF_:Eqv_E_WF A}.
      Context {Ord_:Ord A} {OrdWF_:OrdWF A}.
      Context {Lattice_:Lattice A} {LatticeWF_:LatticeWF A}.
      Context {BLattice_:BoundedLattice A} {BLatticeWF_:BoundedLatticeWF A}.

      Global Instance DTKS_Lattice : Lattice (T A) :=
        { lmeet := from '..' (lmeet `on` to)
        ; ljoin := from '..' (ljoin `on` to)
        }.
      Global Instance DTKS_InjectionDistribute_lmeet_eq
          : InjectionDistribute (T A) (U A) to lmeet lmeet eq :=
        DerivingInjectionDistribute to from lmeet lmeet eq eq_refl.
      Global Instance DTKS_InjectionDistribute_lmeet_eqv
          : InjectionDistribute (T A) (U A) to lmeet lmeet eqv :=
        DerivingInjectionDistribute_ext to lmeet lmeet eq eqv.
      Global Instance DTKS_InjectionDistribute_ljoin_eq
          : InjectionDistribute (T A) (U A) to ljoin ljoin eq :=
        DerivingInjectionDistribute to from ljoin ljoin eq eq_refl.
      Global Instance DTKS_InjectionDistribute_ljoin_eqv
          : InjectionDistribute (T A) (U A) to ljoin ljoin eqv :=
        DerivingInjectionDistribute_ext to ljoin ljoin eq eqv.
      Global Instance DTKS_LatticeWF : LatticeWF (T A) :=
        DerivingLatticeWF to.

      Global Instance DTKS_BoundedLattice : BoundedLattice (T A) :=
        { ltop := from ltop
        ; lbot := from lbot
        }.
      Global Instance DTKS_BoundedLatticeWF : BoundedLatticeWF (T A) :=
        DerivingBoundedLatticeWF to from eq_refl eq_refl.
    End Lattice.
  End Context.
End DerivingTheKitchenSink1.

Class depend {T} (X:T) := {}.
Instance : forall {T} {X:T}, depend X := {}.

Module Type DerivingTheKitchenSink2_Arg.
  Parameter T : (Type -> Type) -> Type -> Type.
  Parameter U : (Type -> Type) -> Type -> Type.
  Parameter to : forall {m A}, T m A -> U m A.
  Parameter from : forall {m A}, U m A -> T m A.
  Parameter InjResp : forall {m A}, InjectionRespect (T m A) (U m A) to eq eq.
  Parameter InjInv : forall {m A}, InjectionInverse (U m A) (T m A) from to eq.
  Section m.
    Context {m:Type->Type}.
    Global Declare Instance U_EqDec :
      forall
        {EqDec_m :
           forall {X} {EqDec_:EqDec X},
           EqDec (m X)}
        {A} {EqDec_:EqDec A},
      EqDec (U m A).
    Global Declare Instance U_EqDec_RDC :
      forall
        {EqDec_m :
           forall {X} {EqDec_:EqDec X},
           EqDec (m X)}
        {EqDec_RDC_m :
           forall {X} {EqDec_:EqDec X} {EqDec_RDC_:RelDecCorrect X eq eq_dec},
           RelDecCorrect (m X) eq eq_dec}
        {A} {EqDec_:EqDec A} {RDC_A:RelDecCorrect A eq eq_dec},
      RelDecCorrect (U m A) eq eq_dec.
    Global Declare Instance U_Eqv :
      forall
        {Eqv_m :
           forall {X} {Eqv_:Eqv X},
           Eqv (m X)}
        {A} {Eqv_:Eqv A},
      Eqv (U m A).
    Global Declare Instance U_Eqv_PE_WF :
      forall
        {Eqv_m :
           forall {X} {Eqv_:Eqv X},
           Eqv (m X)}
        {Eqv_PE_WF_m :
           forall {X} {Eqv_:Eqv X} {Eqv_PE_WF_:Eqv_PE_WF X},
           Eqv_PE_WF (m X)}
        {A} {Eqv_:Eqv A} {Eqv_PE_WF_:Eqv_PE_WF A},
      Eqv_PE_WF (U m A).
    Global Declare Instance U_Eqv_E_WF :
      forall
        {Eqv_m :
           forall {X} {Eqv_:Eqv X},
           Eqv (m X)}
        {Eqv_E_WF_m :
           forall {X} {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X},
           Eqv_E_WF (m X)}
        {A} {Eqv_:Eqv A} {Eqv_E_WF_:Eqv_E_WF A},
      Eqv_E_WF (U m A).
    Global Declare Instance U_EqvDec :
      forall
        {EqvDec_m :
           forall {X} {EqvDec_:EqvDec X},
            EqvDec (m X)}
        {A} {EqvDec_:EqvDec A},
      EqvDec (U m A).
    Global Declare Instance U_EqvDec_RDC :
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
      RelDecCorrect (U m A) eqv eqv_dec.
    Global Declare Instance U_Ord :
      forall
        {Ord_m :
           forall {X} {Ord_:Ord X},
           Ord (m X)}
        {A} {Ord_:Ord A},
      Ord (U m A).
    Global Declare Instance U_OrdWF :
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
      OrdWF (U m A).
    Global Declare Instance U_OrdDec :
      forall
        {OrdDec_m :
           forall {X} {OrdDec_:OrdDec X},
           OrdDec (m X)}
        {A} {OrdDec_:OrdDec A},
      OrdDec (U m A).
    Global Declare Instance U_ODC :
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
      OrdDecCorrect (U m A).
    Global Declare Instance U_Lattice :
      forall
        {Lattice_m :
           forall {X} {Lattice_:Lattice X},
           Lattice (m X)}
        {A} {Lattice_:Lattice A},
      Lattice (U m A).
    Global Declare Instance U_LatticeWF :
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
      LatticeWF (U m A).
    Global Declare Instance U_BoundedLattice :
      forall 
        {BoundedLattice_m :
           forall {X} {BoundedLattice_:BoundedLattice X},
           BoundedLattice (m X)}
        {A} {BoundedLattice_:BoundedLattice A},
      BoundedLattice (U m A).
    Global Declare Instance U_BoundedLatticeWF :
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
      BoundedLatticeWF (U m A).
  End m.
End DerivingTheKitchenSink2_Arg.

Module DerivingTheKitchenSink2 (X:DerivingTheKitchenSink2_Arg).
  Import X.
  Arguments T _ _ /.
  Arguments U _ _ /.
  Arguments to {m A} _ /.
  Arguments from {m A} _ /.

  Section Context.
    Context {m:Type->Type} {A:Type}.

    Section EqDec.
      Context {EqDec_:EqDec A} {EqDec_RDC_:RelDecCorrect A eq eq_dec}.
      Context {EqDec_m :
        forall {X} {EqDec_:EqDec X},
        EqDec (m X)}.
      Context {EqDec_RDC_m :
        forall {X} {EqDec_:EqDec X} {EqDec_RDC_:RelDecCorrect X eq eq_dec},
        RelDecCorrect (m X) eq eq_dec}.

      Global Instance DTKS_EqDec : EqDec (T m A) := { eq_dec := eq_dec `on` to }.
      Global Instance DTKS_EqDec_RDC : RelDecCorrect (T m A) eq eq_dec :=
        DerivingEqRDC to eq_refl.
    End EqDec.

    Section Eqv.
      Context {Eqv_:Eqv A}.
      Context {Eqv_m :
        forall {X} {Eqv_:Eqv X},
        Eqv (m X)}.

      Global Instance DTKS_Eqv : Eqv (T m A) := { eqv := eqv `on` to }.
      Global Instance DTKS_InjectionRespect_to_eqv
          : InjectionRespect (T m A) (U m A) to eqv eqv :=
        DerivingInjResp to eqv eqv eq_refl.
    End Eqv.

    Section Eqv_PE_WF.
      Context {Eqv_:Eqv A} {EqvWF_:Eqv_PE_WF A}.
      Context {Eqv_m :
        forall {X} {Eqv_:Eqv X},
        Eqv (m X)}.
      Context {Eqv_PE_WF_m :
        forall {X} {Eqv_:Eqv X} {Eqv_PE_WF_:Eqv_PE_WF X},
        Eqv_PE_WF (m X)}.

      Global Instance DTKS_PE_EqvWF : Eqv_PE_WF (T m A) :=
        DerivingEqv_PE_WF to.
      Global Instance DTKS_PE_InjectionRespect_from_eqv
          : InjectionRespect (U m A) (T m A) from eqv eqv :=
        DerivingInjResp_inv from to eqv eqv eq_refl.
    End Eqv_PE_WF.

    Section Eqv_E_WF.
      Context {Eqv_:Eqv A} {EqvWF_:Eqv_E_WF A}.
      Context {Eqv_m :
        forall {X} {Eqv_:Eqv X},
        Eqv (m X)}.
      Context {Eqv_E_WF_m :
        forall {X} {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X},
        Eqv_E_WF (m X)}.

      Global Instance DTKS_E_EqvWF : Eqv_E_WF (T m A) :=
        DerivingEqv_E_WF to.
      Global Instance DTKS_E_InjectionRespect_from_eqv
          : InjectionRespect (U m A) (T m A) from eqv eqv :=
        DerivingInjResp_inv from to eqv eqv eq_refl.
      Global Instance DTKS_InjectionInverse_from_eqv
          : InjectionInverse (U m A) (T m A) from to eqv :=
        DerivingInjectionInverse_ext from to eq eqv.
    End Eqv_E_WF.

    Section EqvDec.
      Context {Eqv_:Eqv A} {EqvDec_:EqvDec A}.
      Context {EqvDec_RDC_:RelDecCorrect A eqv eqv_dec}.
      Context {Eqv_m :
        forall {X} {Eqv_:Eqv X},
        Eqv (m X)}.
      Context {EqvDec_m :
        forall {X} {EqvDec_:EqvDec X},
        EqvDec (m X)}.
      Context {EqvDec_RDC_m :
        forall
          {X} {Eqv_:Eqv X} {EqvDec_:EqvDec X}
          {RDC_A:RelDecCorrect X eqv eqv_dec},
        RelDecCorrect (m X) eqv eqv_dec}.

      Global Instance DTKS_EqvDec : EqvDec (T m A) := { eqv_dec := eqv_dec `on` to }.
      Global Instance DTKS_EqvDec_RDC : RelDecCorrect (T m A) eqv eqv_dec :=
        DerivingRelDec to eqv eqv_dec eqv eqv_dec eq_refl.
    End EqvDec.

    Section Ord.
      Context {Eqv_:Eqv A} {EqvWF_:Eqv_E_WF A}.
      Context {Ord_:Ord A} {OrdWF_:OrdWF A}.
      Context {OrdDec_:OrdDec A} {ODC_:OrdDecCorrect A}.
      Context {Eqv_m :
        forall {X} {Eqv_:Eqv X},
        Eqv (m X)}.
      Context {Eqv_E_WF_m :
        forall {X} {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X},
        Eqv_E_WF (m X)}.
      Context {Ord_m :
        forall {X} {Ord_:Ord X},
        Ord (m X)}.
      Context {OrdWF_m :
        forall
          {X}
          {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X}
          {Ord_:Ord X} {Ord_WF_:OrdWF X},
        OrdWF (m X)}.
      Context {OrdDec_m :
        forall {X} {OrdDec_:OrdDec X},
        OrdDec (m X)}.
      Context {ODC_m :
        forall
          {X} {Eqv_:Eqv X}
          {Ord_:Ord X} {OrdDec_:OrdDec X} {ODC_A:OrdDecCorrect X},
        OrdDecCorrect (m X)}.

      Global Instance DTKS_Ord : Ord (T m A) := { lt := lt `on` to }.
      Global Instance DTKS_InjectionRespect_to_lt
          : InjectionRespect (T m A) (U m A) to lt lt :=
        DerivingInjResp to lt lt eq_refl.
      Global Instance DTKS_InjectionRespect_from_lt
          : InjectionRespect (U m A) (T m A) from lt lt :=
        DerivingInjResp_inv from to lt lt eq_refl.
      Global Instance DTKS_OrdWF : OrdWF (T m A) :=
        DerivingOrdWF to.

      Global Instance DTKS_OrdDec : OrdDec (T m A) := { ord_dec := ord_dec `on` to }.
      Global Instance DTKS_ODC : OrdDecCorrect (T m A) :=
        DerivingOrdDecCorrect to eq_refl.
    End Ord.

    Section Lattice.
      Context {Eqv_:Eqv A} {EqvWF_:Eqv_E_WF A}.
      Context {Ord_:Ord A} {OrdWF_:OrdWF A}.
      Context {Lattice_:Lattice A} {LatticeWF_:LatticeWF A}.
      Context {BLattice_:BoundedLattice A} {BLatticeWF_:BoundedLatticeWF A}.
      Context {Eqv_m :
        forall {X} {Eqv_:Eqv X},
        Eqv (m X)}.
      Context {Eqv_E_WF_m :
        forall {X} {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X},
        Eqv_E_WF (m X)}.
      Context {Ord_m :
        forall {X} {Ord_:Ord X},
        Ord (m X)}.
      Context {OrdWF_m :
        forall
          {X}
          {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X}
          {Ord_:Ord X} {Ord_WF_:OrdWF X},
        OrdWF (m X)}.
      Context {Lattice_m :
        forall {X} {Lattice_:Lattice X},
        Lattice (m X)}.
      Context {LatticeWF_m :
        forall {X}
          {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X}
          {Ord_:Ord X} {OrdWF_:OrdWF X}
          {Lattice_:Lattice X} {LatticeWF_:LatticeWF X},
        LatticeWF (m X)}.
      Context {BoundedLattice_m :
        forall {X} {BoundedLattice_:BoundedLattice X},
        BoundedLattice (m X)}.
      Context {BoundedLatticeWF_m :
        forall {X}
          {Eqv_:Eqv X} {Eqv_E_WF_:Eqv_E_WF X}
          {Ord_:Ord X} {OrdWF_:OrdWF X}
          {Lattice_:Lattice X} {LatticeWF_:LatticeWF X}
          {BoundedLattice_:BoundedLattice X} {BoundedLatticeWF_:BoundedLatticeWF X},
        BoundedLatticeWF (m X)}.

      Global Instance DTKS_Lattice : Lattice (T m A) :=
        { lmeet := from '..' (lmeet `on` to)
        ; ljoin := from '..' (ljoin `on` to)
        }.
      Global Instance DTKS_InjectionDistribute_lmeet_eq
          : InjectionDistribute (T m A) (U m A) to lmeet lmeet eq :=
        DerivingInjectionDistribute to from lmeet lmeet eq eq_refl.
      Global Instance DTKS_InjectionDistribute_lmeet_eqv
          : InjectionDistribute (T m A) (U m A) to lmeet lmeet eqv :=
        DerivingInjectionDistribute_ext to lmeet lmeet eq eqv.
      Global Instance DTKS_InjectionDistribute_ljoin_eq
          : InjectionDistribute (T m A) (U m A) to ljoin ljoin eq :=
        DerivingInjectionDistribute to from ljoin ljoin eq eq_refl.
      Global Instance DTKS_InjectionDistribute_ljoin_eqv
          : InjectionDistribute (T m A) (U m A) to ljoin ljoin eqv :=
        DerivingInjectionDistribute_ext to ljoin ljoin eq eqv.
      Global Instance DTKS_LatticeWF : LatticeWF (T m A) :=
        DerivingLatticeWF to.

      Global Instance DTKS_BoundedLattice : BoundedLattice (T m A) :=
        { ltop := from ltop
        ; lbot := from lbot
        }.
      Global Instance DTKS_BoundedLatticeWF : BoundedLatticeWF (T m A) :=
        DerivingBoundedLatticeWF to from eq_refl eq_refl.
    End Lattice.
  End Context.
End DerivingTheKitchenSink2.
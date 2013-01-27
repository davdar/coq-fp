Require Import FP.Data.Function.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Ord.
Require Import FP.Relations.Setoid.

Import FunctionNotation.

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
  Proof. constructor ; unfold Proper ; simpl ; intros.
    rewrite poof in H ; auto.
    rewrite poof ; auto.
  Qed.
End DerivingInjResp.

Section DerivingInjResp_inv.
  Context {T:Type} {U:Type}.
  Variable (to:T -> U).
  Variable (from:U -> T).
  Variable (TR:T -> T -> Prop) (UR:U -> U -> Prop).
  Context {InjResp2:InjectionRespect U T from UR TR}.
  Variable (eqv:T -> T -> Prop).
  Context {Eqv:Equivalence eqv}.
  Context {InjInv:InjectionInverse T U to from eqv}.
  Context {TR_Resp:Proper (eqv ==> eqv ==> impl) TR}.
  Variable (poof:UR = (TR `on` from)).

  Definition DerivingInjResp_inv : InjectionRespect T U to TR UR.
  Proof. constructor ; unfold Proper ; simpl ; intros.
    rewrite poof ; simpl.
      repeat rewrite <- InjectionInverse_inv ; auto.
    rewrite poof in H ; simpl in H.
      repeat rewrite <- InjectionInverse_inv in H ; auto.
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
  Proof. constructor ; intros.
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
  Proof. repeat (constructor ; simpl in * ; intros).
    rewrite poof.
      apply rel_correct.
      apply InjectionRespect_eta ; auto.
    rewrite poof in H.
      apply dec_correct in H.
      apply InjectionRespect_beta ; auto.
    Qed.
End DerivingEqRDC.

Section DerivingEqvWF.
  Context {T} {T_Eqv:Eqv T} {U} {U_Eqv:Eqv U} {U_EqvWF:EqvWF U}.
  Variable (inj:T -> U).
  Context {T_U_InjResp:InjectionRespect T U inj eqv eqv}.

  Definition DerivingEqvWF : EqvWF T.
  Proof. repeat constructor.
    unfold Reflexive ; intros.
      apply InjectionRespect_beta ; reflexivity.
    unfold Symmetric ; intros.
      apply InjectionRespect_beta ; apply InjectionRespect_eta in H ; symmetry ; auto.
    unfold Transitive ; intros x y z H1 H2.
      apply InjectionRespect_beta.
      apply InjectionRespect_eta in H1 ; apply InjectionRespect_eta in H2.
      transitivity (inj y) ; auto.
  Qed.
End DerivingEqvWF.

Section DerivingOrdWF.
  Context {T} {T_Eqv:Eqv T} {T_EqvWF:EqvWF T} {T_Ord:Ord T}.
  Context {U} {U_Eqv:Eqv U} {U_EqvWF:EqvWF U} {U_Ord:Ord U} {U_OrdWF:OrdWF U}.
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
    unfold Proper ; simpl ; intros.
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
  Context {T_Eqv:Eqv T} {T_EqvWF:EqvWF T}.
  Context {T_Ord:Ord T} {T_OrdWF:OrdWF T}.
  Context {T_Lattice:Lattice T}.
  Context {U:Type}.
  Context {U_Eqv:Eqv U} {U_EqvWF:EqvWF U}.
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
  Context {T_Eqv:Eqv T} {T_EqvWF:EqvWF T}.
  Context {T_Ord:Ord T} {T_OrdWF:OrdWF T}.
  Context {T_Lattice:Lattice T}.
  Context {T_BoundedLattice:BoundedLattice T}.
  Context {U:Type}.
  Context {U_Eqv:Eqv U} {U_EqvWF:EqvWF U}.
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
  Parameter InjResp : forall A, InjectionRespect (T A) (U A) to eq eq.
  Parameter InjInv : forall A, InjectionInverse (U A) (T A) from to eq.
End DerivingTheKitchenSink1_Arg.

Module DerivingTheKitchenSink1 (X:DerivingTheKitchenSink1_Arg).
  Import X.
  Arguments to {A} _ /.
  Arguments from {A} _ /.

  Section Context.
    Context {A:Type}.
    Context {U_EqDec:EqDec (U A)} {U_RDC_eq:RelDecCorrect (U A) eq eq_dec}.
    Context {U_Eqv:Eqv (U A)} {U_EqvWF:EqvWF (U A)}.
    Context {U_EqvDec:EqvDec (U A)} {U_RDC_eqv:RelDecCorrect (U A) eqv eqv_dec}.
    Context {U_Ord:Ord (U A)} {U_OrdWF:OrdWF (U A)}.
    Context {U_OrdDec:OrdDec (U A)} {U_ODC:OrdDecCorrect (U A)}.
    Context {U_Lattice:Lattice (U A)} {U_LatticeWF:LatticeWF (U A)}.
    Context {U_BLattice:BoundedLattice (U A)} {U_BLatticeWF:BoundedLatticeWF (U A)}.

    Global Instance DTKS_EqDec : EqDec (T A) := { eq_dec := eq_dec `on` to }.
    Global Instance DTKS_EqDec_RDC : RelDecCorrect (T A) eq eq_dec :=
      DerivingEqRDC to eq_refl.

    Global Instance DTKS_Eqv : Eqv (T A) := { eqv := eqv `on` to }.
    Global Instance DTKS_InjectionRespect_to_eqv
        : InjectionRespect (T A) (U A) to eqv eqv :=
      DerivingInjResp to eqv eqv eq_refl.
    Global Instance DTKS_InjectionRespect_from_eqv
        : InjectionRespect (U A) (T A) from eqv eqv :=
      DerivingInjResp_inv from to eqv eqv eq eq_refl.
    Global Instance DTKS_EqvWF : EqvWF (T A) :=
      DerivingEqvWF to.
    Global Instance DTKS_InjectionInverse_from_eqv
        : InjectionInverse (U A) (T A) from to eqv :=
      DerivingInjectionInverse_ext from to eq eqv.

    Global Instance DTKS_EqvDec : EqvDec (T A) := { eqv_dec := eqv_dec `on` to }.
    Global Instance DTKS_EqvDec_RDC : RelDecCorrect (T A) eqv eqv_dec :=
      DerivingRelDec to eqv eqv_dec eqv eqv_dec eq_refl.

    Global Instance DTKS_Ord : Ord (T A) := { lt := lt `on` to }.
    Global Instance DTKS_InjectionRespect_to_lt
        : InjectionRespect (T A) (U A) to lt lt :=
      DerivingInjResp to lt lt eq_refl.
    Global Instance DTKS_InjectionRespect_from_lt
        : InjectionRespect (U A) (T A) from lt lt :=
      DerivingInjResp_inv from to lt lt eq eq_refl.
    Global Instance DTKS_OrdWF : OrdWF (T A) :=
      DerivingOrdWF to.

    Global Instance DTKS_OrdDec : OrdDec (T A) := { ord_dec := ord_dec `on` to }.
    Global Instance DTKS_ODC : OrdDecCorrect (T A) :=
      DerivingOrdDecCorrect to eq_refl.

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
  End Context.
End DerivingTheKitchenSink1.
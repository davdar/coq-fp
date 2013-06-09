Require Import FP.CoreData.
Require Import FP.CoreClasses.

Import CoreDataNotation.
Import CoreClassesNotation.

Section Deriving_RDC.
  Context {T U} inj TR TD UR UD
    `{! InjectionRespect T U inj TR UR
     ,! RelDecCorrect U UR UD
     }
    `(! TD = (UD `on` inj) ).

  Definition Deriving_RDC : RelDecCorrect T TR TD.
  Proof. constructor ; intros.
    - rewrite H ; simpl.
      apply InjectionRespect_eta in H0.
      apply rel_correct ; auto.
    - rewrite H in H0 ; simpl in H0.
      apply InjectionRespect_beta.
      apply dec_correct ; auto.
  Qed.
End Deriving_RDC.

Section Deriving_IR.
  Context {T U} inj (TR:T->T->Prop) (UR:U->U->Prop)
    `(! TR = (UR `on` inj) ).

  Definition Deriving_IR : InjectionRespect T U inj TR UR.
  Proof. constructor ; unfold Proper,"==>","<==" ; simpl ; intros.
    rewrite H in H0 ; auto.
    rewrite H ; unfold on ; simpl ; auto.
  Qed.
End Deriving_IR.

Section Deriving_IR_inv.
  Context {T U} to from TR UR
    `{! PER TR
     ,! InjectionRespect T U to UR TR
     ,! InjectionInverse U T from to eq
     }
    `(! UR = (TR `on` to) ).

  Definition Deriving_IR_inv : InjectionRespect U T from TR UR.
  Proof.
    constructor ; unfold Proper,"==>","<==" ; simpl ; intros.
    - rewrite H ; simpl.
      repeat (rewrite InjectionInverse_inv ; logical_eqv).
    - rewrite H in H0 ; simpl in H0.
      repeat (rewrite InjectionInverse_inv in H0 ; logical_eqv).
  Qed.
End Deriving_IR_inv.

Section Deriving_II_ext.
  Context {T U} to from R1 R2
    `{! Equivalence R1
     ,! Equivalence R2
     ,! InjectionInverse T U to from R1
     ,! Proper (R1 ==> R1 ==> impl) R2
     }.

  Definition Deriving_II_ext : InjectionInverse T U to from R2.
  Proof. constructor ; intros.
    eapply Proper0.
    - symmetry ; apply InjectionInverse_inv ; logical_eqv.
    - reflexivity.
    - reflexivity.
  Qed.
End Deriving_II_ext.

Section Deriving_ID.
  Context {T U} to from TM UM
    `{! InjectionInverse U T from to eq }
    `(! TM = (from '.:' (UM `on` to)) ).

  Definition Deriving_ID : InjectionDistribute T U to TM UM eq.
  Proof. constructor ; intros.
    rewrite H ; simpl.
    apply InjectionInverse_inv ; logical_eqv.
  Qed.
End Deriving_ID.

Section Deriving_ID_ext.
  Context {T U} to TM UM eqv1 eqv2
    `{! Equivalence eqv1 ,! Equivalence eqv2
     ,! InjectionDistribute T U to TM UM eqv1
     ,! Proper (eqv1 ==> eqv1 ==> impl) eqv2
     }.

  Definition Deriving_ID_ext : InjectionDistribute T U to TM UM eqv2.
  Proof.
    constructor ; intros.
    rewrite InjectionDistribute_law.
    reflexivity.
  Qed.
End Deriving_ID_ext.

Section Deriving_Eq_RDC.
  Context {T U} inj
    `{! EqDec T ,! EqDec U
     ,! Eq_RDC U
     ,! InjectionRespect T U inj eq eq
     }
    `(! eq_dec = (eq_dec `on` inj) ).

  Definition Deriving_Eq_RDC : Eq_RDC T.
  Proof.
    repeat (constructor ; simpl in * ; intros).
    - rewrite H ; simpl.
      apply rel_correct.
      apply InjectionRespect_eta ; auto.
    - rewrite H in H0 ; simpl in H0.
      apply dec_correct in H0.
      apply InjectionRespect_beta ; auto.
    Qed.
End Deriving_Eq_RDC.

Section Deriving_PER_WF.
  Context {T U} inj
    `{! Eqv T ,! Eqv U ,! PER_WF U
     ,! InjectionRespect T U inj eqv eqv
     }.

  Definition Deriving_PER_WF : PER_WF T.
  Proof.
    repeat constructor.
    - unfold Symmetric ; intros.
      apply InjectionRespect_beta ; apply InjectionRespect_eta in H ; symmetry ; auto.
    - unfold Transitive ; intros x y z H1 H2.
      apply InjectionRespect_beta.
      apply InjectionRespect_eta in H1 ; apply InjectionRespect_eta in H2.
      transitivity (inj y) ; auto.
  Qed.
End Deriving_PER_WF.

Section Deriving_ER_WF.
  Context {T U} inj
    `{! Eqv T ,! Eqv U ,! ER_WF U
     ,! InjectionRespect T U inj eqv eqv
     }.

  Definition Deriving_ER_WF : ER_WF T.
  Proof.
    repeat constructor.
    - unfold Reflexive ; intros.
      apply InjectionRespect_beta ; reflexivity.
    - unfold Symmetric ; intros.
      apply InjectionRespect_beta ; apply InjectionRespect_eta in H ; symmetry ; auto.
    - unfold Transitive ; intros x y z H1 H2.
      apply InjectionRespect_beta.
      apply InjectionRespect_eta in H1 ; apply InjectionRespect_eta in H2.
      transitivity (inj y) ; auto.
  Qed.
End Deriving_ER_WF.

Section Deriving_Lte_RDC.
  Context {T U} inj
    `{! Lte T ,! LteDec T ,! Lte U ,! LteDec U ,! Lte_RDC U
     ,! InjectionRespect T U inj lte lte
     }
    `(! lte_dec = (lte_dec `on` inj) ).

  Definition Deriving_Lte_RDC : Lte_RDC T.
  Proof.
    repeat constructor ; intros.
    - rewrite H ; simpl.
      apply InjectionRespect_eta in H0.
      apply rel_correct in H0 ; auto.
    - rewrite H in H0 ; simpl in H0.
      apply InjectionRespect_beta.
      apply dec_correct ; auto.
  Qed.
End Deriving_Lte_RDC.

Section Deriving_PreOrd.
  Context {T U} inj
    `{! Lte T ,! Lte U ,! PreOrd U
     ,! InjectionRespect T U inj lte lte
     }.

  Definition Deriving_PreOrd : PreOrd T.
  Proof.
    constructor. 
    - unfold Reflexive ; intros.
      apply InjectionRespect_beta.
      reflexivity.
    - unfold Transitive ; intros.
      apply InjectionRespect_beta.
      apply InjectionRespect_eta in H.
      apply InjectionRespect_eta in H0.
      transitivity (inj y) ; auto.
  Qed.
End Deriving_PreOrd.

Section Deriving_PartialOrd.
  Context {T U} inj
    `{! Lte T ,! Eqv T ,! ER_WF T ,! PreOrd T
     ,! Lte U ,! Eqv U ,! ER_WF U ,! PartialOrd U
     ,! InjectionRespect T U inj eqv eqv
     ,! InjectionRespect T U inj lte lte
     }.

  Definition Deriving_PartialOrd : PartialOrd T.
  Proof.
    constructor.
    - eauto with typeclass_instances.
    - unfold Antisymmetric ; intros.
      apply InjectionRespect_beta.
      apply InjectionRespect_eta in H.
      apply InjectionRespect_eta in H0.
      apply PartialOrd_Antisymmetry ; auto.
    - unfold Proper,"==>",impl,Basics.impl ; intros.
      apply InjectionRespect_beta.
      apply InjectionRespect_eta in H.
      apply InjectionRespect_eta in H0.
      apply InjectionRespect_eta in H1.
      eapply PartialOrd_respect_eqv.
      apply H.
      apply H0.
      apply H1.
  Qed.
End Deriving_PartialOrd.

Section Deriving_PartialOrd_RDC.
  Context {T U} inj
    `{! Lte T ,! Eqv T ,! ER_WF T ,! PartialOrd T ,! PartialOrdDec T
     ,! Lte U ,! Eqv U ,! ER_WF U ,! PartialOrd U ,! PartialOrdDec U ,! PartialOrd_RDC U
     ,! InjectionRespect T U inj eqv eqv
     ,! InjectionRespect T U inj lte lte
     }
    `(! pord_dec = (pord_dec `on` inj) ).

  Definition Deriving_PartialOrd_RDC : PartialOrd_RDC T.
  Proof.
    constructor ; intros ; try rewrite H ; try rewrite H in H0 ; simpl in *.
    - apply InjectionRespect_eta in H0.
      apply pord_rel_correct_eqv ; auto.
    - apply InjectionRespect_eta in H0.
      apply pord_rel_correct_lt ; auto.
    - apply InjectionRespect_eta in H0.
      apply pord_rel_correct_gt ; auto.
    - apply InjectionRespect_eta in H0.
      apply pord_rel_correct_un ; auto.
    - apply InjectionRespect_beta.
      apply pord_dec_correct_eqv ; auto.
    - apply InjectionRespect_beta.
      apply pord_dec_correct_lt ; auto.
    - apply InjectionRespect_beta.
      apply pord_dec_correct_gt ; auto.
    - apply InjectionRespect_beta.
      apply pord_dec_correct_un ; auto.
  Qed.
End Deriving_PartialOrd_RDC.

Section Deriving_TotalOrd.
  Context {T U} (inj:T->U)
   `{! Lte T ,! Eqv T ,! ER_WF T ,! PartialOrd T
    ,! Lte U ,! Eqv U ,! ER_WF U ,! TotalOrd U
    ,! InjectionRespect T U inj lte lte
    }.
  Definition Deriving_TotalOrd : TotalOrd T.
  Proof.
    constructor ; eauto with typeclass_instances.
    intros.
    unfold "~" at 1 ; intros pun ; destruct pun.
    apply (TotalOrd_comparable (inj x) (inj y)) ; constructor
    ; unfold "~" ; intros H1 ; apply InjectionRespect_beta in H1 ; contradiction.
  Qed.
End Deriving_TotalOrd.

Section Deriving_TotalOrd_RDC.
  Context {T U} inj
    `{! Lte T ,! Eqv T ,! ER_WF T ,! TotalOrd T ,! TotalOrdDec T
     ,! Lte U ,! Eqv U ,! ER_WF U ,! TotalOrd U ,! TotalOrdDec U ,! TotalOrd_RDC U
     ,! InjectionRespect T U inj eqv eqv
     ,! InjectionRespect T U inj lte lte
     }
    `(! tord_dec = (tord_dec `on` inj) ).

  Definition Deriving_TotalOrd_RDC : TotalOrd_RDC T.
  Proof.
    constructor ; intros ; try rewrite H ; try rewrite H in H0 ; simpl in *.
    - apply InjectionRespect_eta in H0.
      apply tord_rel_correct_eqv ; auto.
    - apply InjectionRespect_eta in H0.
      apply tord_rel_correct_lt ; auto.
    - apply InjectionRespect_eta in H0.
      apply tord_rel_correct_gt ; auto.
    - apply InjectionRespect_beta.
      apply tord_dec_correct_eqv ; auto.
    - apply InjectionRespect_beta.
      apply tord_dec_correct_lt ; auto.
    - apply InjectionRespect_beta.
      apply tord_dec_correct_gt ; auto.
  Qed.
End Deriving_TotalOrd_RDC.

Section Deriving_LatticeWF.
  Context {T U} inj
    `{! Eqv T ,! Lte T ,! ER_WF T ,! PartialOrd T ,! Lattice T
     ,! Eqv U ,! Lte U ,! ER_WF U ,! PartialOrd U ,! Lattice U ,! LatticeWF U
     ,! InjectionRespect T U inj lte lte
     ,! InjectionDistribute T U inj lmeet lmeet eqv
     ,! InjectionDistribute T U inj ljoin ljoin eqv
     }.

  Definition Deriving_LatticeWF : LatticeWF T.
  Proof.
    constructor ; intros ; constructor
    ; apply InjectionRespect_beta ; rewrite InjectionDistribute_law.
    - apply lmeet_ineq.
    - apply lmeet_ineq.
    - apply ljoin_ineq.
    - apply ljoin_ineq.
  Qed.
End Deriving_LatticeWF.

Section Deriving_BoundedLatticeWF.
  Context {T U} to from
    `{! Lte T ,! Eqv T ,! ER_WF T ,! PartialOrd T ,! Lattice T ,! BoundedLattice T
     ,! Lte U ,! Eqv U ,! ER_WF U ,! PartialOrd U ,! Lattice U ,! BoundedLattice U ,! BoundedLatticeWF U
     ,! InjectionRespect T U to eqv eqv
     ,! InjectionRespect T U to lte lte
     ,! InjectionRespect U T from lte lte
     ,! InjectionInverse U T from to eqv
     }
    `(! ltop = from ltop
     ,! lbot = from lbot
     ).

  Definition Deriving_BoundedLatticeWF : BoundedLatticeWF T.
  Proof.
    constructor ; intros.
    - rewrite H.
      apply InjectionRespect_beta.
      rewrite  InjectionInverse_inv ; logical_eqv.
      apply ltop_ineq.
    - rewrite H0.
      apply InjectionRespect_beta.
      rewrite InjectionInverse_inv ; logical_eqv.
      apply lbot_ineq.
  Qed.
End Deriving_BoundedLatticeWF.
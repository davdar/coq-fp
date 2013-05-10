Require Import FP.CoreClasses.PartialOrd.
Require Import FP.CoreClasses.TotalOrd.
Require Import FP.CoreClasses.EqDec.
Require Import FP.CoreClasses.Eqv.
Require Import FP.CoreClasses.PreOrd.
Require Import FP.CoreClasses.Lattice.

(***** EqDec *****)
Class F_EqDec t :=
  { f_eq_dec :> forall {A} `{! EqDec A }, EqDec (t A) }.
Class Bif_EqDec t :=
  { bif_eq_dec :> forall {A B} `{! EqDec A ,! EqDec B }, EqDec (t A B) }.

(***** Eq_RDC *****)
Class F_Eq_RDC t `{! F_EqDec t } :=
  { f_eq_rdc :> forall {A} `{! EqDec A ,! Eq_RDC A }, Eq_RDC (t A) }.
Class Bif_Eq_RDC t `{! Bif_EqDec t } :=
  { bif_eq_rdc :> forall {A B} `{! EqDec A ,! Eq_RDC A ,! EqDec B ,! Eq_RDC B }, Eq_RDC (t A B) }.

(***** Eqv *****)
Class F_Eqv t :=
  { f_eqv :> forall {A} `{! Eqv A }, Eqv (t A) }.
Class Bif_Eqv t :=
  { bif_eqv :> forall {A B} `{! Eqv A ,! Eqv B }, Eqv (t A B) }.

(***** PER_WF *****)
Class F_PER_WF t `{! F_Eqv t } :=
  { f_per_wf :> forall {A} `{! Eqv A ,! PER_WF A }, PER_WF (t A) }.
Class Bif_PER_WF t `{! Bif_Eqv t } :=
  { bif_per_wf :> forall {A B} `{! Eqv A ,! PER_WF A ,! Eqv B ,! PER_WF B }, PER_WF (t A B) }.

(***** ER_WF *****)
Class F_ER_WF t `{! F_Eqv t } :=
  { f_er_wf :> forall {A} `{! Eqv A ,! ER_WF A }, ER_WF (t A) }.
Class Bif_ER_WF t `{! Bif_Eqv t } :=
  { bif_er_wf :> forall {A B} `{! Eqv A ,! ER_WF A ,! Eqv B ,! ER_WF B }, ER_WF (t A B) }.

(***** EqvDec *****)
Class F_EqvDec t :=
  { f_eqv_dec :> forall {A} `{! EqvDec A }, EqvDec (t A) }.
Class Bif_EqvDec t :=
  { bif_eqv_dec :> forall {A B} `{! EqvDec A ,! EqvDec B }, EqvDec (t A B) }.

(***** Eqv_RDC *****)
Class F_Eqv_RDC t `{! F_Eqv t ,! F_EqvDec t } :=
  { f_eqv_rdc :> forall {A} `{! Eqv A ,! EqvDec A ,! Eqv_RDC A }, Eqv_RDC (t A) }.
Class Bif_Eqv_RDC t `{! Bif_Eqv t ,! Bif_EqvDec t } :=
  { bif_eqv_rdc :> forall {A B} `{! Eqv A ,! EqvDec A ,! Eqv_RDC A ,! Eqv B ,! EqvDec B ,! Eqv_RDC B }, Eqv_RDC (t A B) }.

(***** Lte *****)
Class F_Lte t :=
  { f_lte :> forall {A} `{! Lte A }, Lte (t A) }.
Class Bif_Lte t :=
  { bif_lte :> forall {A B} `{! Lte A ,! Lte B }, Lte (t A B) }.

(***** PreOrd *****)
Class F_PreOrd t `{! F_Lte t } :=
  { f_pre_ord :> forall {A} `{! Lte A ,! PreOrd A }, PreOrd (t A) }.
Class Bif_PreOrd t `{! Bif_Lte t } :=
  { bif_pre_ord :> forall {A B} `{! Lte A ,! PreOrd A ,! Lte B ,! PreOrd B }, PreOrd (t A B) }.

(***** LteDec *****)
Class F_LteDec t :=
  { f_lte_dec :> forall {A} `{! LteDec A }, LteDec (t A) }.
Class Bif_LteDec t :=
  { bif_lte_dec :> forall {A B} `{! LteDec A ,! LteDec B }, LteDec (t A B) }.

(***** Lte_RDC *****)
Class F_Lte_RDC t `{! F_Lte t ,! F_LteDec t } :=
  { f_lte_rdc :> forall {A} `{! Lte A ,! LteDec A ,! Lte_RDC A }, Lte_RDC (t A) }.
Class Bif_Lte_RDC t `{! Bif_Lte t ,! Bif_LteDec t } :=
  { bif_lte_rdc :> forall {A B} `{! Lte A ,! LteDec A ,! Lte_RDC A ,! Lte B ,! LteDec B ,! Lte_RDC B }, Lte_RDC (t A B) }.

(***** PartialOrd *****)
Class F_PartialOrd t `{! F_Lte t ,! F_Eqv t ,! F_ER_WF t } :=
  { f_partial_ord :> forall {A} `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A }, PartialOrd (t A)
  ; f_partial_ord_pre_ord :> F_PreOrd t
  }.
Class Bif_PartialOrd t `{! Bif_Lte t ,! Bif_Eqv t ,! Bif_ER_WF t } :=
  { bif_partial_ord :> forall {A B}
                         `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A
                          ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B }, PartialOrd (t A B)
  ; bif_partial_ord_pre_ord :> Bif_PreOrd t
  }.

(***** PartialOrdDec *****)
Class F_PartialOrdDec t :=
  { f_partial_ord_dec :> forall {A} `{! PartialOrdDec A }, PartialOrdDec (t A) }.
Class Bif_PartialOrdDec t :=
  { bif_partial_ord_dec :> forall {A B} `{! PartialOrdDec A ,! PartialOrdDec B }, PartialOrdDec (t A B) }.

(***** PartialOrdDecCorrect ****)
Class F_PartialOrd_RDC t `{! F_Lte t ,! F_Eqv t ,! F_ER_WF t ,! F_PartialOrd t ,! F_PartialOrdDec t }:=
  { f_partial_ord_rdc :>
      forall {A} `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! PartialOrdDec A ,! PartialOrd_RDC A },
      PartialOrd_RDC (t A) }.
Class Bif_PartialOrd_RDC t `{! Bif_Lte t ,! Bif_Eqv t ,! Bif_ER_WF t ,! Bif_PartialOrd t ,! Bif_PartialOrdDec t }:=
  { bif_partial_ord_rdc :> forall {A B}
                             `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! PartialOrdDec A ,! PartialOrd_RDC A
                              ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B ,! PartialOrdDec B ,! PartialOrd_RDC B
                              }, PartialOrd_RDC (t A B) }.

(***** TotalOrd *****)
Class F_TotalOrd t `{! F_Lte t ,! F_Eqv t ,! F_ER_WF t } :=
  { f_total_ord :> forall {A} `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A }, TotalOrd (t A)
  ; f_total_ord_partial_ord :> F_PartialOrd t
  }.
Class Bif_TotalOrd t `{! Bif_Lte t ,! Bif_Eqv t ,! Bif_ER_WF t } :=
  { bif_total_ord :> forall {A B}
                       `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A
                        ,! Lte B ,! Eqv B ,! ER_WF B ,! TotalOrd B }, TotalOrd (t A B)
  ; bif_total_ord_partial_ord :> Bif_PartialOrd t
  }.

(***** TotalOrdDec *****)
Class F_TotalOrdDec t :=
  { f_total_ord_dec :> forall {A} `{! TotalOrdDec A }, TotalOrdDec (t A) }.
Class Bif_TotalOrdDec t :=
  { bif_total_ord_dec :> forall {A B} `{! TotalOrdDec A ,! TotalOrdDec B }, TotalOrdDec (t A B) }.

(***** TotalOrd_RDC *****)
Class F_TotalOrd_RDC t `{! F_Lte t ,! F_Eqv t ,! F_ER_WF t ,! F_TotalOrd t ,! F_TotalOrdDec t } :=
  { f_total_ord_rdc :>
      forall {A} `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! TotalOrdDec A ,! TotalOrd_RDC A },
      TotalOrd_RDC (t A) }.
Class Bif_TotalOrd_RDC t `{! Bif_Lte t ,! Bif_Eqv t ,! Bif_ER_WF t ,! Bif_TotalOrd t ,! Bif_TotalOrdDec t } :=
  { bif_total_ord_rdc :> forall {A B}
                           `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! TotalOrdDec A ,! TotalOrd_RDC A
                            ,! Lte B ,! Eqv B ,! ER_WF B ,! TotalOrd B ,! TotalOrdDec B ,! TotalOrd_RDC B
                            }, TotalOrd_RDC (t A B) }.

(***** Lattice *****)
Class F_Lattice t :=
  { f_lattice :> forall {A} `{! Lattice A }, Lattice (t A) }.
Class Bif_Lattice t :=
  { bif_lattice :> forall {A B} `{! Lattice A ,! Lattice B }, Lattice (t A B) }.

(***** LatticeWF *****)
Class F_LatticeWF t `{! F_Lte t ,! F_Eqv t ,! F_ER_WF t ,! F_PartialOrd t ,! F_Lattice t } :=
  { f_lattice_wf :> forall {A} `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! Lattice A ,! LatticeWF A }, LatticeWF (t A) }.
Class Bif_LatticeWF t `{! Bif_Lte t ,! Bif_Eqv t ,! Bif_ER_WF t ,! Bif_PartialOrd t ,! Bif_Lattice t } :=
  { bif_lattice_wf :> forall {A B}
                        `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! Lattice A ,! LatticeWF A
                         ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B ,! Lattice B ,! LatticeWF B
                         }, LatticeWF (t A B) }.

(***** BoundedLattice *****)
Class F_BoundedLattice t :=
  { f_bounded_lattice :> forall {A} `{! BoundedLattice A }, BoundedLattice (t A) }.
Class Bif_BoundedLattice t :=
  { bif_bounded_lattice :> forall {A B} `{! BoundedLattice A ,! BoundedLattice B }, BoundedLattice (t A B) }.

(***** BoundedLatticeWF *****)
Class F_BoundedLatticeWF t
    `{! F_Lte t ,! F_Eqv t ,! F_ER_WF t ,! F_PartialOrd t ,! F_Lattice t ,! F_BoundedLattice t,! F_LatticeWF t } :=
  { f_bounded_lattice_wf :> forall {A}
                              `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A
                               ,! Lattice A ,! BoundedLattice A ,! LatticeWF A ,! BoundedLatticeWF A
                               }, BoundedLatticeWF (t A) }.
Class Bif_BoundedLatticeWF t
    `{! Bif_Lte t ,! Bif_Eqv t ,! Bif_ER_WF t ,! Bif_PartialOrd t ,! Bif_Lattice t ,! Bif_BoundedLattice t,! Bif_LatticeWF t } :=
  { bif_bounded_lattice_wf :> forall {A B}
                                `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A
                                 ,! Lattice A ,! BoundedLattice A ,! LatticeWF A ,! BoundedLatticeWF A
                                 ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B
                                 ,! Lattice B ,! BoundedLattice B ,! LatticeWF B ,! BoundedLatticeWF B
                                 }, BoundedLatticeWF (t A B) }.
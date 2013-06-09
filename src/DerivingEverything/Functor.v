Require Import FP.DerivingEverything.Core.
Require Import FP.CoreClasses.
Require Import FP.CoreData.

Import CoreDataNotation.

Class DE_FunctorI U :=
  { DE_F_EqDec :>
      forall {A}
        `{! EqDec A
         }, EqDec (U A)
  ; DE_F_Eq_RDC :>
      forall {A}
         `{! EqDec A ,! Eq_RDC A
          }, Eq_RDC (U A)
  ; DE_F_Eqv :>
      forall {A}
        `{! Eqv A
         }, Eqv (U A)
  ; DE_F_PER_WF :>
      forall {A}
        `{! Eqv A ,! PER_WF A
         }, PER_WF (U A)
  ; DE_F_ER_WF :>
      forall {A}
        `{! Eqv A ,! ER_WF A
         }, ER_WF (U A)
  ; DE_F_EqvDec :>
      forall {A}
        `{! EqvDec A
         }, EqvDec (U A)
  ; DE_F_Eqv_RDC :>
      forall {A}
        `{! Eqv A ,! EqvDec A ,! Eqv_RDC A
         }, Eqv_RDC (U A)
  ; DE_F_Lte :>
      forall {A}
        `{! Lte A
         }, Lte (U A)
  ; DE_F_PreOrd :>
      forall {A}
        `{! Lte A ,! PreOrd A
         }, PreOrd (U A)
  ; DE_F_LteDec :>
      forall {A}
        `{! LteDec A
         }, LteDec (U A)
  ; DE_F_Lte_RDC :>
      forall {A}
        `{! Lte A ,! LteDec A ,! Lte_RDC A
         }, Lte_RDC (U A)
  ; DE_F_PartialOrd :>
      forall {A}
        `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A
         }, PartialOrd (U A)
  ; DE_F_PartialOrdDec :>
      forall {A}
        `{! PartialOrdDec A
         }, PartialOrdDec (U A)
  ; DE_F_PartialOrd_RDC :>
      forall {A}
        `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! PartialOrdDec A ,! PartialOrd_RDC A
         }, PartialOrd_RDC (U A)
  ; DE_F_TotalOrd :>
      forall {A}
        `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A
         }, TotalOrd (U A)
  ; DE_F_TotalOrdDec :>
      forall {A}
        `{! TotalOrdDec A
         }, TotalOrdDec (U A)
  ; DE_F_TotalOrd_RDC :>
      forall {A}
        `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! TotalOrdDec A ,! TotalOrd_RDC A
         }, TotalOrd_RDC (U A)
  ; DE_F_Lattice :>
      forall {A}
        `{! Lattice A
         }, Lattice (U A)
  ; DE_F_LatticeWF :>
      forall {A}
        `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! Lattice A ,! LatticeWF A
         }, LatticeWF (U A)
  ; DE_F_BoundedLattice :>
      forall {A}
        `{! BoundedLattice A
         }, BoundedLattice (U A)
  ; DE_F_BoundedLatticeWF :>
      forall {A}
        `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A
         ,! Lattice A ,! BoundedLattice A ,! LatticeWF A ,! BoundedLatticeWF A
         }, BoundedLatticeWF (U A)
  }.

Class DE_FunctorI' U := { de_functor_i : DE_FunctorI U }.

Module Type DE_Functor_Arg.
  Parameter T : Type -> Type.
  Parameter U : Type -> Type.
  Parameter to : forall {A}, T A -> U A.
  Parameter from : forall {A}, U A -> T A.
  Parameter IR_to : forall {A}, InjectionRespect (T A) (U A) to eq eq.
  Parameter II_from : forall {A}, InjectionInverse (U A) (T A) from to eq.
  Parameter _DE_FunctorI : DE_FunctorI' U.
End DE_Functor_Arg.

Module DE_Functor (M:DE_Functor_Arg).
  Local Existing Instance de_functor_i.

  Import M.
  Arguments T / _.
  Arguments U / _.
  Arguments to {A} / _.
  Arguments from {A} / _.

  Section Eq.
    Context {A} `{! EqDec A ,! Eq_RDC A }.

    Global Instance _EqDec : EqDec (T A) := { eq_dec := eq_dec `on` to }.
    Global Instance _Eq_RDC : Eq_RDC (T A) := Deriving_Eq_RDC to eq_refl.
  End Eq.
  Global Instance _F_EqDec : F_EqDec T := { f_eq_dec := @_EqDec }.
  Global Instance _F_Eq_RDC : F_Eq_RDC T := { f_eq_rdc := @_Eq_RDC }.

  Section Eqv.
    Context {A} `{! Eqv A ,! EqvDec A ,! Eqv_RDC A }.

    Global Instance _Eqv : Eqv (T A) := { eqv := eqv `on` to }.
    Global Instance _IR_to_eqv : InjectionRespect (T A) (U A) to eqv eqv :=
      Deriving_IR to eqv eqv eq_refl.
    Global Instance _EqvDec : EqvDec (T A) := { eqv_dec := eqv_dec `on` to }.
    Global Instance _Eqv_RDC : Eqv_RDC (T A) :=
      { eqv_rdc := Deriving_RDC to eqv eqv_dec eqv eqv_dec eq_refl }.
  End Eqv.
  Global Instance _F_Eqv : F_Eqv T := { f_eqv := @_Eqv }.
  Global Instance _F_EqvDec : F_EqvDec T := { f_eqv_dec := @_EqvDec }.
  Global Instance _F_Eqv_RDC : F_Eqv_RDC T := { f_eqv_rdc := @_Eqv_RDC }.

  Section PER_WF.
    Context {A} `{! Eqv A ,! PER_WF A }.

    Global Instance _PER_WF : PER_WF (T A) := Deriving_PER_WF to.
    Global Instance _IR_from_eqv_PER : InjectionRespect (U A) (T A) from eqv eqv :=
      Deriving_IR_inv to from eqv eqv eq_refl.
  End PER_WF.
  Global Instance _F_PER_WF : F_PER_WF T := { f_per_wf := @_PER_WF }.

  Section ER_WF.
    Context {A} `{! Eqv A ,! ER_WF A }.

    Global Instance _ER_WF : ER_WF (T A) := Deriving_ER_WF to.
    Global Instance _IR_from_eqv_ER : InjectionRespect (U A) (T A) from eqv eqv :=
      Deriving_IR_inv to from eqv eqv eq_refl.
    Global Instance _II_from_eqv_ER : InjectionInverse (U A) (T A) from to eqv :=
      Deriving_II_ext from to eq eqv.
  End ER_WF.
  Global Instance _F_ER_WF : F_ER_WF T := { f_er_wf := @_ER_WF }.

  Section PreOrd.
    Context {A} `{! Lte A ,! PreOrd A ,! LteDec A ,! Lte_RDC A }.

    Global Instance _Lte : Lte (T A) := { lte := lte `on` to }.
    Global Instance _IR_to_lte : InjectionRespect (T A) (U A) to lte lte :=
      Deriving_IR to lte lte eq_refl.
    Global Instance _PreOrd : PreOrd (T A) := Deriving_PreOrd to.
    Global Instance _LteDec : LteDec (T A) := { lte_dec := lte_dec `on` to }.
    Global Instance _Lte_RDC : Lte_RDC (T A) := Deriving_Lte_RDC to eq_refl.
  End PreOrd.
  Global Instance _F_Lte : F_Lte T := { f_lte := @_Lte }.
  Global Instance _F_PreOrd : F_PreOrd T := { f_pre_ord := @_PreOrd }.
  Global Instance _F_LteDec : F_LteDec T := { f_lte_dec := @_LteDec }.
  Global Instance _F_Lte_RDC : F_Lte_RDC T := { f_lte_rdc := @_Lte_RDC }.

  Section PartialOrd.
    Context {A} `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! PartialOrdDec A ,! PartialOrd_RDC A }.

    Global Instance _PartialOrd : PartialOrd (T A) := Deriving_PartialOrd to.
    Global Instance _PartialOrdDec : PartialOrdDec (T A) := { pord_dec := pord_dec `on` to }.
    Global Instance _PartialOrd_RDC : PartialOrd_RDC (T A) := Deriving_PartialOrd_RDC to eq_refl.
  End PartialOrd.
  Global Instance _F_PartialOrd : F_PartialOrd T := { f_partial_ord := @_PartialOrd }.
  Global Instance _F_PartialOrdDec : F_PartialOrdDec T := { f_partial_ord_dec := @_PartialOrdDec }.
  Global Instance _F_PartialOrd_RDC : F_PartialOrd_RDC T := { f_partial_ord_rdc := @_PartialOrd_RDC }.

  Section TotalOrd.
    Context {A} `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! TotalOrdDec A ,! TotalOrd_RDC A }.

    Global Instance _TotalOrd : TotalOrd (T A) := Deriving_TotalOrd to.
    Global Instance _TotalOrdDec : TotalOrdDec (T A) := { tord_dec := tord_dec `on` to }.
    Global Instance _TotalOrd_RDC : TotalOrd_RDC (T A) := Deriving_TotalOrd_RDC to eq_refl.
  End TotalOrd.
  Global Instance _F_TotalOrd : F_TotalOrd T := { f_total_ord := @_TotalOrd }.
  Global Instance _F_TotalOrdDec : F_TotalOrdDec T := { f_total_ord_dec := @_TotalOrdDec }.
  Global Instance _F_TotalOrd_RDC : F_TotalOrd_RDC T := { f_total_ord_rdc := @_TotalOrd_RDC }.

  Section Lattice.
    Context {A}
      `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A
       ,! Lattice A ,! BoundedLattice A ,! LatticeWF A ,! BoundedLatticeWF A
       }.
    Global Instance _Lattice : Lattice (T A) :=
      { lmeet := from '.:' (lmeet `on` to)
      ; ljoin := from '.:' (ljoin `on` to)
      }.
    Global Instance _ID_lmeet_eq : InjectionDistribute (T A) (U A) to lmeet lmeet eq :=
      Deriving_ID to from lmeet lmeet eq_refl.
    Global Instance _ID_lmeet_eqv : InjectionDistribute (T A) (U A) to lmeet lmeet eqv :=
      Deriving_ID_ext to lmeet lmeet eq eqv.
    Global Instance _ID_ljoin_eq : InjectionDistribute (T A) (U A) to ljoin ljoin eq :=
      Deriving_ID to from ljoin ljoin eq_refl.
    Global Instance _ID_ljoin_eqv : InjectionDistribute (T A) (U A) to ljoin ljoin eqv :=
      Deriving_ID_ext to ljoin ljoin eq eqv.
    Global Instance _LatticeWF : LatticeWF (T A) := Deriving_LatticeWF to.

    Global Instance _BoundedLattice : BoundedLattice (T A) :=
      { ltop := from ltop
      ; lbot := from lbot
      }.
    Global Instance _BoundedLatticeWF : BoundedLatticeWF (T A) :=
      Deriving_BoundedLatticeWF to from eq_refl eq_refl.
  End Lattice.
  Global Instance _F_Lattice : F_Lattice T := { f_lattice := @_Lattice }.
  Global Instance _F_LatticeWF : F_LatticeWF T := { f_lattice_wf := @_LatticeWF }.
  Global Instance _F_BoundedLattice : F_BoundedLattice T := { f_bounded_lattice := @_BoundedLattice }.
  Global Instance _F_BoundedLatticeWF : F_BoundedLatticeWF T := { f_bounded_lattice_wf := @_BoundedLatticeWF }.
End DE_Functor.
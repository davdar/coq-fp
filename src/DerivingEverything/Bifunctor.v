Require Import FP.DerivingEverything.Core.
Require Import FP.CoreClasses.
Require Import FP.CoreData.

Import CoreDataNotation.

Class DE_BifunctorI U :=
  { DE_Bif_EqDec :>
      forall {A B}
        `{! EqDec A
         ,! EqDec B
         }, EqDec (U A B)
  ; DE_Bif_Eq_RDC :>
      forall {A B}
         `{! EqDec A ,! Eq_RDC A
          ,! EqDec B ,! Eq_RDC B
          }, Eq_RDC (U A B)
  ; DE_Bif_Eqv :>
      forall {A B}
        `{! Eqv A
         ,! Eqv B
         }, Eqv (U A B)
  ; DE_Bif_PER_WF :>
      forall {A B}
        `{! Eqv A ,! PER_WF A
         ,! Eqv B ,! PER_WF B
         }, PER_WF (U A B)
  ; DE_Bif_ER_WF :>
      forall {A B}
        `{! Eqv A ,! ER_WF A
         ,! Eqv B ,! ER_WF B
         }, ER_WF (U A B)
  ; DE_Bif_EqvDec :>
      forall {A B}
        `{! EqvDec A
         ,! EqvDec B
         }, EqvDec (U A B)
  ; DE_Bif_Eqv_RDC :>
      forall {A B}
        `{! Eqv A ,! EqvDec A ,! Eqv_RDC A
         ,! Eqv B ,! EqvDec B ,! Eqv_RDC B
         }, Eqv_RDC (U A B)
  ; DE_Bif_Lte :>
      forall {A B}
        `{! Lte A
         ,! Lte B
         }, Lte (U A B)
  ; DE_Bif_PreOrd :>
      forall {A B}
        `{! Lte A ,! PreOrd A
         ,! Lte B ,! PreOrd B
         }, PreOrd (U A B)
  ; DE_Bif_LteDec :>
      forall {A B}
        `{! LteDec A
         ,! LteDec B
         }, LteDec (U A B)
  ; DE_Bif_Lte_RDC :>
      forall {A B}
        `{! Lte A ,! LteDec A ,! Lte_RDC A
         ,! Lte B ,! LteDec B ,! Lte_RDC B
         }, Lte_RDC (U A B)
  ; DE_Bif_PartialOrd :>
      forall {A B}
        `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A
         ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B
         }, PartialOrd (U A B)
  ; DE_Bif_PartialOrdDec :>
      forall {A B}
        `{! PartialOrdDec A
         ,! PartialOrdDec B
         }, PartialOrdDec (U A B)
  ; DE_Bif_PartialOrd_RDC :>
      forall {A B}
        `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! PartialOrdDec A ,! PartialOrd_RDC A
         ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B ,! PartialOrdDec B ,! PartialOrd_RDC B
         }, PartialOrd_RDC (U A B)
  ; DE_Bif_TotalOrd :>
      forall {A B}
        `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A
         ,! Lte B ,! Eqv B ,! ER_WF B ,! TotalOrd B
         }, TotalOrd (U A B)
  ; DE_Bif_TotalOrdDec :>
      forall {A B}
        `{! TotalOrdDec A
         ,! TotalOrdDec B
         }, TotalOrdDec (U A B)
  ; DE_Bif_TotalOrd_RDC :>
      forall {A B}
        `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! TotalOrdDec A ,! TotalOrd_RDC A
         ,! Lte B ,! Eqv B ,! ER_WF B ,! TotalOrd B ,! TotalOrdDec B ,! TotalOrd_RDC B
         }, TotalOrd_RDC (U A B)
  ; DE_Bif_Lattice :>
      forall {A B}
        `{! Lattice A
         ,! Lattice B
         }, Lattice (U A B)
  ; DE_Bif_LatticeWF :>
      forall {A B}
        `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! Lattice A ,! LatticeWF A
         ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B ,! Lattice B ,! LatticeWF B
         }, LatticeWF (U A B)
  ; DE_Bif_BoundedLattice :>
      forall {A B}
        `{! BoundedLattice A
         ,! BoundedLattice B
         }, BoundedLattice (U A B)
  ; DE_Bif_BoundedLatticeWF :>
      forall {A B}
        `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A
         ,! Lattice A ,! BoundedLattice A ,! LatticeWF A ,! BoundedLatticeWF A
         ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B
         ,! Lattice B ,! BoundedLattice B ,! LatticeWF B ,! BoundedLatticeWF B
         }, BoundedLatticeWF (U A B)
  }.

Module Type DE_Bifunctor_Arg.
  Parameter T : Type -> Type -> Type.
  Parameter U : Type -> Type -> Type.
  Parameter to : forall {A B}, T A B -> U A B.
  Parameter from : forall {A B}, U A B -> T A B.
  Parameter IR_to : forall {A B}, InjectionRespect (T A B) (U A B) to eq eq.
  Parameter II_from : forall {A B}, InjectionInverse (U A B) (T A B) from to eq.
  Global Declare Instance _DE_BifunctorI : DE_BifunctorI U.
End DE_Bifunctor_Arg.

Module DE_Bifunctor (M:DE_Bifunctor_Arg).
  Import M.
  Arguments T _ _ /.
  Arguments U _ _ /.
  Arguments to {A B} _ /.
  Arguments from {A B} _ /.

  Section Eq.
    Context {A B} `{! EqDec A ,! Eq_RDC A ,! EqDec B ,! Eq_RDC B }.

    Global Instance _EqDec : EqDec (T A B) := { eq_dec := eq_dec `on` to }.
    Global Instance _Eq_RDC : Eq_RDC (T A B) := Deriving_Eq_RDC to eq_refl.
  End Eq.
  Global Instance _Bif_EqDec : Bif_EqDec T := { bif_eq_dec := @_EqDec }.
  Global Instance _Bif_Eq_RDC : Bif_Eq_RDC T := { bif_eq_rdc := @_Eq_RDC }.

  Section Eqv.
    Context {A B} `{! Eqv A ,! EqvDec A ,! Eqv_RDC A ,! Eqv B ,! EqvDec B ,! Eqv_RDC B }.

    Global Instance _Eqv : Eqv (T A B) := { eqv := eqv `on` to }.
    Global Instance _IR_to_eqv : InjectionRespect (T A B) (U A B) to eqv eqv :=
      Deriving_IR to eqv eqv eq_refl.
    Global Instance _EqvDec : EqvDec (T A B) := { eqv_dec := eqv_dec `on` to }.
    Global Instance _Eqv_RDC : Eqv_RDC (T A B) :=
      { eqv_rdc := Deriving_RDC to eqv eqv_dec eqv eqv_dec eq_refl }.
  End Eqv.
  Global Instance _Bif_Eqv : Bif_Eqv T := { bif_eqv := @_Eqv }.
  Global Instance _Bif_EqvDec : Bif_EqvDec T := { bif_eqv_dec := @_EqvDec }.
  Global Instance _Bif_Eqv_RDC : Bif_Eqv_RDC T := { bif_eqv_rdc := @_Eqv_RDC }.

  Section PER_WF.
    Context {A B} `{! Eqv A ,! PER_WF A ,! Eqv B ,! PER_WF B }.

    Global Instance _PER_WF : PER_WF (T A B) := Deriving_PER_WF to.
    Global Instance _IR_from_eqv_PER : InjectionRespect (U A B) (T A B) from eqv eqv :=
      Deriving_IR_inv to from eqv (eqv (T:=T A B)) eq_refl.
  End PER_WF.
  Global Instance _Bif_PER_WF : Bif_PER_WF T := { bif_per_wf := @_PER_WF }.

  Section ER_WF.
    Context {A B} `{! Eqv A ,! ER_WF A ,! Eqv B ,! ER_WF B }.

    Global Instance _ER_WF : ER_WF (T A B) := Deriving_ER_WF to.
    Global Instance _IR_from_eqv_ER : InjectionRespect (U A B) (T A B) from eqv eqv :=
      Deriving_IR_inv to from eqv (eqv (T:=T A B)) eq_refl.
    Global Instance _II_from_eqv_ER : InjectionInverse (U A B) (T A B) from to eqv :=
      Deriving_II_ext from to eq eqv.
  End ER_WF.
  Global Instance _Bif_ER_WF : Bif_ER_WF T := { bif_er_wf := @_ER_WF }.

  Section PreOrd.
    Context {A B}
      `{! Lte A ,! PreOrd A ,! LteDec A ,! Lte_RDC A
       ,! Lte B ,! PreOrd B ,! LteDec B ,! Lte_RDC B
       }.

    Global Instance _Lte : Lte (T A B) := { lte := lte `on` to }.
    Global Instance _IR_to_lte : InjectionRespect (T A B) (U A B) to lte lte :=
      Deriving_IR to lte lte eq_refl.
    Global Instance _PreOrd : PreOrd (T A B) := Deriving_PreOrd to.
    Global Instance _LteDec : LteDec (T A B) := { lte_dec := lte_dec `on` to }.
    Global Instance _Lte_RDC : Lte_RDC (T A B) := Deriving_Lte_RDC to eq_refl.
  End PreOrd.
  Global Instance _Bif_Lte : Bif_Lte T := { bif_lte := @_Lte }.
  Global Instance _Bif_PreOrd : Bif_PreOrd T := { bif_pre_ord := @_PreOrd }.
  Global Instance _Bif_LteDec : Bif_LteDec T := { bif_lte_dec := @_LteDec }.
  Global Instance _Bif_Lte_RDC : Bif_Lte_RDC T := { bif_lte_rdc := @_Lte_RDC }.

  Section PartialOrd.
    Context {A B}
      `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! PartialOrdDec A ,! PartialOrd_RDC A
       ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B ,! PartialOrdDec B ,! PartialOrd_RDC B
       }.

    Global Instance _PartialOrd : PartialOrd (T A B) := Deriving_PartialOrd to.
    Global Instance _PartialOrdDec : PartialOrdDec (T A B) := { pord_dec := pord_dec `on` to }.
    Global Instance _PartialOrd_RDC : PartialOrd_RDC (T A B) :=
      Deriving_PartialOrd_RDC (to:T A B -> U A B) eq_refl.
  End PartialOrd.
  Global Instance _Bif_PartialOrd : Bif_PartialOrd T := { bif_partial_ord := @_PartialOrd }.
  Global Instance _Bif_PartialOrdDec : Bif_PartialOrdDec T := { bif_partial_ord_dec := @_PartialOrdDec }.
  Global Instance _Bif_PartialOrd_RDC : Bif_PartialOrd_RDC T := { bif_partial_ord_rdc := @_PartialOrd_RDC }.

  Section TotalOrd.
    Context {A B}
      `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! TotalOrdDec A ,! TotalOrd_RDC A
       ,! Lte B ,! Eqv B ,! ER_WF B ,! TotalOrd B ,! TotalOrdDec B ,! TotalOrd_RDC B
       }.

    Global Instance _TotalOrd : TotalOrd (T A B) := Deriving_TotalOrd to.
    Global Instance _TotalOrdDec : TotalOrdDec (T A B) := { tord_dec := tord_dec `on` to }.
    Global Instance _TotalOrd_RDC : TotalOrd_RDC (T A B) :=
      Deriving_TotalOrd_RDC (to:T A B -> U A B) eq_refl.
  End TotalOrd.
  Global Instance _Bif_TotalOrd : Bif_TotalOrd T := { bif_total_ord := @_TotalOrd }.
  Global Instance _Bif_TotalOrdDec : Bif_TotalOrdDec T := { bif_total_ord_dec := @_TotalOrdDec }.
  Global Instance _Bif_TotalOrd_RDC : Bif_TotalOrd_RDC T := { bif_total_ord_rdc := @_TotalOrd_RDC }.

  Section Lattice.
    Context {A B}
      `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A
       ,! Lattice A ,! BoundedLattice A ,! LatticeWF A ,! BoundedLatticeWF A
       ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B
       ,! Lattice B ,! BoundedLattice B ,! LatticeWF B ,! BoundedLatticeWF B
       }.
    Global Instance _Lattice : Lattice (T A B) :=
      { lmeet := from '.:' (lmeet `on` to)
      ; ljoin := from '.:' (ljoin `on` to)
      }.
    Global Instance _ID_lmeet_eq : InjectionDistribute (T A B) (U A B) to lmeet lmeet eq :=
      Deriving_ID to from lmeet lmeet eq_refl.
    Global Instance _ID_lmeet_eqv : InjectionDistribute (T A B) (U A B) to lmeet lmeet eqv :=
      Deriving_ID_ext to lmeet lmeet eq eqv.
    Global Instance _ID_ljoin_eq : InjectionDistribute (T A B) (U A B) to ljoin ljoin eq :=
      Deriving_ID to from ljoin ljoin eq_refl.
    Global Instance _ID_ljoin_eqv : InjectionDistribute (T A B) (U A B) to ljoin ljoin eqv :=
      Deriving_ID_ext to ljoin ljoin eq eqv.
    Global Instance _LatticeWF : LatticeWF (T A B) := Deriving_LatticeWF to.

    Global Instance _BoundedLattice : BoundedLattice (T A B) :=
      { ltop := from ltop
      ; lbot := from lbot
      }.
    Global Instance _BoundedLatticeWF : BoundedLatticeWF (T A B) :=
      Deriving_BoundedLatticeWF (to:T A B -> U A B) from eq_refl eq_refl.
  End Lattice.
  Global Instance _Bif_Lattice : Bif_Lattice T := { bif_lattice := @_Lattice }.
  Global Instance _Bif_LatticeWF : Bif_LatticeWF T := { bif_lattice_wf := @_LatticeWF }.
  Global Instance _Bif_BoundedLattice : Bif_BoundedLattice T := { bif_bounded_lattice := @_BoundedLattice }.
  Global Instance _Bif_BoundedLatticeWF : Bif_BoundedLatticeWF T := { bif_bounded_lattice_wf := @_BoundedLatticeWF }.
End DE_Bifunctor.
Require Import FP.DerivingEverything.Core.
Require Import FP.CoreClasses.
Require Import FP.CoreData.

Import CoreDataNotation.

Class DE_IdxFunctorI U :=
  { DE_IF_EqDec :>
      forall {I A}
        `{! EqDec I
         ,! EqDec A
         }, EqDec (U I A)
  ; DE_IF_Eq_RDC :>
      forall {I A}
         `{! EqDec I ,! Eq_RDC I
          ,! EqDec A ,! Eq_RDC A
          }, Eq_RDC (U I A)
  ; DE_IF_Eqv :>
      forall {I A}
        `{! Eqv I
         ,! Eqv A
         }, Eqv (U I A)
  ; DE_IF_PER_WF :>
      forall {I A}
        `{! Eqv I ,! PER_WF I
         ,! Eqv A ,! PER_WF A
         }, PER_WF (U I A)
  ; DE_IF_ER_WF :>
      forall {I A}
        `{! Eqv I ,! ER_WF I
         ,! Eqv A ,! ER_WF A
         }, ER_WF (U I A)
  ; DE_IF_EqvDec :>
      forall {I A}
        `{! EqvDec I
         ,! EqvDec A
         }, EqvDec (U I A)
  ; DE_IF_Eqv_RDC :>
      forall {I A}
        `{! Eqv I ,! EqvDec I ,! Eqv_RDC I
         ,! Eqv A ,! EqvDec A ,! Eqv_RDC A
         }, Eqv_RDC (U I A)
  ; DE_IF_Lte :>
      forall {I A}
        `{! Lte I
         ,! Lte A
         }, Lte (U I A)
  ; DE_IF_PreOrd :>
      forall {I A}
        `{! Lte I ,! PreOrd I
         ,! Lte A ,! PreOrd A
         }, PreOrd (U I A)
  ; DE_IF_LteDec :>
      forall {I A}
        `{! LteDec I
         ,! LteDec A
         }, LteDec (U I A)
  ; DE_IF_Lte_RDC :>
      forall {I A}
        `{! Lte I ,! LteDec I ,! Lte_RDC I
         ,! Lte A ,! LteDec A ,! Lte_RDC A
         }, Lte_RDC (U I A)
  ; DE_IF_PartialOrd :>
      forall {I A}
        `{! Lte I ,! Eqv I ,! ER_WF I ,! PartialOrd I
         ,! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A
         }, PartialOrd (U I A)
  ; DE_IF_PartialOrdDec :>
      forall {I A}
        `{! PartialOrdDec I
         ,! PartialOrdDec A
         }, PartialOrdDec (U I A)
  ; DE_IF_PartialOrd_RDC :>
      forall {I A}
        `{! Lte I ,! Eqv I ,! ER_WF I ,! PartialOrd I ,! PartialOrdDec I ,! PartialOrd_RDC I
         ,! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! PartialOrdDec A ,! PartialOrd_RDC A
         }, PartialOrd_RDC (U I A)
  ; DE_IF_TotalOrd :>
      forall {I A}
        `{! Lte I ,! Eqv I ,! ER_WF I ,! TotalOrd I
         ,! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A
         }, TotalOrd (U I A)
  ; DE_IF_TotalOrdDec :>
      forall {I A}
        `{! TotalOrdDec I
         ,! TotalOrdDec A
         }, TotalOrdDec (U I A)
  ; DE_IF_TotalOrd_RDC :>
      forall {I A}
        `{! Lte I ,! Eqv I ,! ER_WF I ,! TotalOrd I ,! TotalOrdDec I ,! TotalOrd_RDC I
         ,! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! TotalOrdDec A ,! TotalOrd_RDC A
         }, TotalOrd_RDC (U I A)
  ; DE_IF_Lattice :>
      forall {I A}
        `{! Lattice I
         ,! Lattice A
         }, Lattice (U I A)
  ; DE_IF_LatticeWF :>
      forall {I A}
        `{! Lte I ,! Eqv I ,! ER_WF I ,! PartialOrd I ,! Lattice I ,! LatticeWF I
         ,! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! Lattice A ,! LatticeWF A
         }, LatticeWF (U I A)
  ; DE_IF_BoundedLattice :>
      forall {I A}
        `{! BoundedLattice I
         ,! BoundedLattice A
         }, BoundedLattice (U I A)
  ; DE_IF_BoundedLatticeWF :>
      forall {I A}
        `{! Lte I ,! Eqv I ,! ER_WF I ,! PartialOrd I
         ,! Lattice I ,! BoundedLattice I ,! LatticeWF I ,! BoundedLatticeWF I
         ,! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A
         ,! Lattice A ,! BoundedLattice A ,! LatticeWF A ,! BoundedLatticeWF A
         }, BoundedLatticeWF (U I A)
  }.

Class DE_IdxFunctorI' U := { de_idx_functor_i : DE_IdxFunctorI U }.

Module Type DE_IdxFunctor_Arg.
  Parameter T : Type -> Type -> Type.
  Parameter U : Type -> Type -> Type.
  Parameter to : forall {I A}, T I A -> U I A.
  Parameter from : forall {I A}, U I A -> T I A.
  Parameter IR_to : forall {I A}, InjectionRespect (T I A) (U I A) to eq eq.
  Parameter II_from : forall {I A}, InjectionInverse (U I A) (T I A) from to eq.
  Parameter _DE_IdxFunctorI : DE_IdxFunctorI' U.
End DE_IdxFunctor_Arg.

Module DE_IdxFunctor (M:DE_IdxFunctor_Arg).
  Local Existing Instance de_idx_functor_i.

  Import M.
  Arguments T / _ _ .
  Arguments U / _ _ .
  Arguments to {I A} / _ .
  Arguments from {I A} / _ .

  Section m.
    Context {I:Type}.

    Section m_Eq.
      Context `{! EqDec I ,! Eq_RDC I }.

      Section Eq.
        Context {A} `{! EqDec A ,! Eq_RDC A }.

        Global Instance _EqDec : EqDec (T I A) := { eq_dec := eq_dec `on` to }.
        Global Instance _Eq_RDC : Eq_RDC (T I A) := Deriving_Eq_RDC to eq_refl.
      End Eq.
      Global Instance _F_EqDec : F_EqDec (T I) := { f_eq_dec := @_EqDec }.
      Global Instance _F_Eq_RDC : F_Eq_RDC (T I) := { f_eq_rdc := @_Eq_RDC }.
    End m_Eq.

    Section m_Eqv.
      Context `{! Eqv I ,! EqvDec I ,! Eqv_RDC I }.

      Section Eqv.
        Context {A} `{! Eqv A ,! EqvDec A ,! Eqv_RDC A }.

        Global Instance _Eqv : Eqv (T I A) := { eqv := eqv `on` to }.
        Global Instance _IR_to_eqv : InjectionRespect (T I A) (U I A) to eqv eqv :=
          Deriving_IR to eqv eqv eq_refl.
        Global Instance _EqvDec : EqvDec (T I A) := { eqv_dec := eqv_dec `on` to }.
        Global Instance _Eqv_RDC : Eqv_RDC (T I A) :=
          { eqv_rdc := Deriving_RDC to eqv eqv_dec eqv eqv_dec eq_refl }.
      End Eqv.
      Global Instance _F_Eqv : F_Eqv (T I) := { f_eqv := @_Eqv }.
      Global Instance _F_EqvDec : F_EqvDec (T I) := { f_eqv_dec := @_EqvDec }.
      Global Instance _F_Eqv_RDC : F_Eqv_RDC (T I) := { f_eqv_rdc := @_Eqv_RDC }.
    End m_Eqv.

    Section m_PER_WF.
      Context `{! Eqv I ,! PER_WF I }.

      Section PER_WF.
        Context {A} `{! Eqv A ,! PER_WF A }.

        Global Instance _PER_WF : PER_WF (T I A) := Deriving_PER_WF to.
        Global Instance _IR_from_eqv_PER : InjectionRespect (U I A) (T I A) from eqv eqv :=
          Deriving_IR_inv to from eqv (eqv (T:=T I A)) eq_refl.
      End PER_WF.
      Global Instance _F_PER_WF : F_PER_WF (T I) := { f_per_wf := @_PER_WF }.
    End m_PER_WF.

    Section m_ER_WF.
      Context `{! Eqv I ,! ER_WF I }.

      Section ER_WF.
        Context {A} `{! Eqv A ,! ER_WF A }.

        Global Instance _ER_WF : ER_WF (T I A) := Deriving_ER_WF to.
        Global Instance _IR_from_eqv_ER : InjectionRespect (U I A) (T I A) from eqv eqv :=
          Deriving_IR_inv to from eqv (eqv (T:=T I A)) eq_refl.
        Global Instance _II_from_eqv_ER : InjectionInverse (U I A) (T I A) from to eqv :=
          Deriving_II_ext from to eq eqv.
      End ER_WF.
      Global Instance _F_ER_WF : F_ER_WF (T I) := { f_er_wf := @_ER_WF }.
    End m_ER_WF.

    Section m_PreOrd.
      Context `{! Lte I ,! PreOrd I ,! LteDec I ,! Lte_RDC I }.

      Section PreOrd.
        Context {A} `{! Lte A ,! PreOrd A ,! LteDec A ,! Lte_RDC A}.

        Global Instance _Lte : Lte (T I A) := { lte := lte `on` to }.
        Global Instance _IR_to_lte : InjectionRespect (T I A) (U I A) to lte lte :=
          Deriving_IR to lte lte eq_refl.
        Global Instance _PreOrd : PreOrd (T I A) := Deriving_PreOrd to.
        Global Instance _LteDec : LteDec (T I A) := { lte_dec := lte_dec `on` to }.
        Global Instance _Lte_RDC : Lte_RDC (T I A) := Deriving_Lte_RDC to eq_refl.
      End PreOrd.
      Global Instance _F_Lte : F_Lte (T I) := { f_lte := @_Lte }.
      Global Instance _F_PreOrd : F_PreOrd (T I) := { f_pre_ord := @_PreOrd }.
      Global Instance _F_LteDec : F_LteDec (T I) := { f_lte_dec := @_LteDec }.
      Global Instance _F_Lte_RDC : F_Lte_RDC (T I) := { f_lte_rdc := @_Lte_RDC }.
    End m_PreOrd.

    Section m_PartialOrd.
      Context `{! Lte I ,! Eqv I ,! ER_WF I ,! PartialOrd I ,! PartialOrdDec I ,! PartialOrd_RDC I }.

      Section PartialOrd.
        Context {A} `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! PartialOrdDec A ,! PartialOrd_RDC A }.

        Global Instance _PartialOrd : PartialOrd (T I A) := Deriving_PartialOrd to.
        Global Instance _PartialOrdDec : PartialOrdDec (T I A) := { pord_dec := pord_dec `on` to }.
        Global Instance _PartialOrd_RDC : PartialOrd_RDC (T I A) :=
          Deriving_PartialOrd_RDC (to:T I A -> U I A) eq_refl.
      End PartialOrd.
      Global Instance _F_PartialOrd : F_PartialOrd (T I) := { f_partial_ord := @_PartialOrd }.
      Global Instance _F_PartialOrdDec : F_PartialOrdDec (T I) := { f_partial_ord_dec := @_PartialOrdDec }.
      Global Instance _F_PartialOrd_RDC : F_PartialOrd_RDC (T I) := { f_partial_ord_rdc := @_PartialOrd_RDC }.
    End m_PartialOrd.

    Section m_TotalOrd.
      Context `{! Lte I ,! Eqv I ,! ER_WF I ,! TotalOrd I ,! TotalOrdDec I ,! TotalOrd_RDC I }.

      Section TotalOrd.
        Context {A} `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! TotalOrdDec A ,! TotalOrd_RDC A }.

        Global Instance _TotalOrd : TotalOrd (T I A) := Deriving_TotalOrd to.
        Global Instance _TotalOrdDec : TotalOrdDec (T I A) := { tord_dec := tord_dec `on` to }.
        Global Instance _TotalOrd_RDC : TotalOrd_RDC (T I A) :=
          Deriving_TotalOrd_RDC (to:T I A -> U I A) eq_refl.
      End TotalOrd.
      Global Instance _F_TotalOrd : F_TotalOrd (T I) := { f_total_ord := @_TotalOrd }.
      Global Instance _F_TotalOrdDec : F_TotalOrdDec (T I) := { f_total_ord_dec := @_TotalOrdDec }.
      Global Instance _F_TotalOrd_RDC : F_TotalOrd_RDC (T I) := { f_total_ord_rdc := @_TotalOrd_RDC }.
    End m_TotalOrd.

    Section m_Lattice.
      Context
        `{! Lte I ,! Eqv I ,! ER_WF I ,! PartialOrd I
         ,! Lattice I ,! BoundedLattice I ,! LatticeWF I ,! BoundedLatticeWF I
         }.

      Section Lattice.
        Context {A}
          `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A
           ,! Lattice A ,! BoundedLattice A ,! LatticeWF A ,! BoundedLatticeWF A
           }.
        Global Instance _Lattice : Lattice (T I A) :=
          { lmeet := from '.:' (lmeet `on` to)
          ; ljoin := from '.:' (ljoin `on` to)
          }.
        Global Instance _ID_lmeet_eq : InjectionDistribute (T I A) (U I A) to lmeet lmeet eq :=
          Deriving_ID to from lmeet lmeet eq_refl.
        Global Instance _ID_lmeet_eqv : InjectionDistribute (T I A) (U I A) to lmeet lmeet eqv :=
          Deriving_ID_ext to lmeet lmeet eq eqv.
        Global Instance _ID_ljoin_eq : InjectionDistribute (T I A) (U I A) to ljoin ljoin eq :=
          Deriving_ID to from ljoin ljoin eq_refl.
        Global Instance _ID_ljoin_eqv : InjectionDistribute (T I A) (U I A) to ljoin ljoin eqv :=
          Deriving_ID_ext to ljoin ljoin eq eqv.
        Global Instance _LatticeWF : LatticeWF (T I A) := Deriving_LatticeWF to.

        Global Instance _BoundedLattice : BoundedLattice (T I A) :=
          { ltop := from ltop
          ; lbot := from lbot
          }.
        Global Instance _BoundedLatticeWF : BoundedLatticeWF (T I A) :=
          Deriving_BoundedLatticeWF (to:T I A -> U I A) from eq_refl eq_refl.
      End Lattice.
      Global Instance _F_Lattice : F_Lattice (T I) := { f_lattice := @_Lattice }.
      Global Instance _F_LatticeWF : F_LatticeWF (T I) := { f_lattice_wf := @_LatticeWF }.
      Global Instance _F_BoundedLattice : F_BoundedLattice (T I) := { f_bounded_lattice := @_BoundedLattice }.
      Global Instance _F_BoundedLatticeWF : F_BoundedLatticeWF (T I) := { f_bounded_lattice_wf := @_BoundedLatticeWF }.
    End m_Lattice.
  End m.
End DE_IdxFunctor.

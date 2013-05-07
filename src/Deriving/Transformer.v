Require Import FP.Deriving.Core.
Require Import FP.CoreClasses.
Require Import FP.CoreData.

Import CoreDataNotation.

Class DerivingEverything_TransformerI U :=
  { DE_Tr_EqDec :> forall {m} `{! F_EqDec m }, F_EqDec (U m)
  ; DE_Tr_Eq_RDC :> forall {m} `{! F_EqDec m ,! F_Eq_RDC m }, F_Eq_RDC (U m)
  ; DE_Tr_Eqv :> forall {m} `{! F_Eqv m }, F_Eqv (U m)
  ; DE_Tr_PER_WF :> forall {m} `{! F_Eqv m ,! F_PER_WF m }, F_PER_WF (U m)
  ; DE_Tr_ER_WF :> forall {m} `{! F_Eqv m ,! F_ER_WF m }, F_ER_WF (U m)
  ; DE_Tr_EqvDec :> forall {m} `{! F_EqvDec m }, F_EqvDec (U m)
  ; DE_Tr_Eqv_RDC :> forall {m} `{! F_Eqv m ,! F_EqvDec m ,! F_Eqv_RDC m }, F_Eqv_RDC (U m)
  ; DE_Tr_Lte :> forall {m} `{! F_Lte m }, F_Lte (U m)
  ; DE_Tr_PreOrd :> forall {m} `{! F_Lte m ,! F_PreOrd m }, F_PreOrd (U m)
  ; DE_Tr_LteDec :> forall {m} `{! F_LteDec m }, F_LteDec (U m)
  ; DE_Tr_Lte_RDC :> forall {m} `{! F_Lte m ,! F_LteDec m ,! F_Lte_RDC m }, F_Lte_RDC (U m)
  ; DE_Tr_PartialOrd :>
      forall {m} `{! F_Lte m ,! F_Eqv m ,! F_ER_WF m ,! F_PartialOrd m }, F_PartialOrd (U m)
  ; DE_Tr_PartialOrdDec :> forall {m} `{! F_PartialOrdDec m }, F_PartialOrdDec (U m)
  ; DE_Tr_PartialOrd_RDC :>
      forall {m} `{! F_Lte m ,! F_Eqv m ,! F_ER_WF m ,! F_PartialOrd m
                  ,! F_PartialOrdDec m ,! F_PartialOrd_RDC m }, F_PartialOrd_RDC (U m)
  ; DE_Tr_TotalOrd :>
      forall {m} `{! F_Lte m ,! F_Eqv m ,! F_ER_WF m ,! F_TotalOrd m }, F_TotalOrd (U m)
  ; DE_Tr_TotalOrdDec :> forall {m} `{! F_TotalOrdDec m }, F_TotalOrdDec (U m)
  ; DE_Tr_TotalOrd_RDC :>
      forall {m} `{! F_Lte m ,! F_Eqv m ,! F_ER_WF m ,! F_TotalOrd m
                  ,! F_TotalOrdDec m ,! F_TotalOrd_RDC m }, F_TotalOrd_RDC (U m)
  ; DE_Tr_Lattice :> forall {m} `{! F_Lattice m }, F_Lattice (U m)
  ; DE_Tr_LatticeWF :>
      forall {m} `{! F_Lte m ,! F_Eqv m ,! F_ER_WF m ,! F_PartialOrd m
                  ,! F_Lattice m ,! F_LatticeWF m }, F_LatticeWF (U m)
  ; DE_Tr_BoundedLattice :> forall {m} `{! F_BoundedLattice m }, F_BoundedLattice (U m)
  ; DE_Tr_BoundedLatticeWF :>
      forall {m} `{! F_Lte m ,! F_Eqv m ,! F_ER_WF m ,! F_PartialOrd m
                  ,! F_Lattice m ,! F_BoundedLattice m
                  ,! F_LatticeWF m ,! F_BoundedLatticeWF m }, F_BoundedLatticeWF (U m)
  }.

Module Type DerivingEverything_Transformer_Arg.
  Parameter T : (Type -> Type) -> Type -> Type.
  Parameter U : (Type -> Type) -> Type -> Type.
  Parameter to : forall {m A}, T m A -> U m A.
  Parameter from : forall {m A}, U m A -> T m A.
  Parameter InjResp : forall {m A}, InjectionRespect (T m A) (U m A) to eq eq.
  Parameter InjInv : forall {m A}, InjectionInverse (U m A) (T m A) from to eq.
  Global Declare Instance _DerivingEverything_TransformerI : DerivingEverything_TransformerI U.
End DerivingEverything_Transformer_Arg.

Module DerivingEverything_Transformer (M:DerivingEverything_Transformer_Arg).
  Import M.
  Arguments T _ _ /.
  Arguments U _ _ /.
  Arguments to {m A} _ /.
  Arguments from {m A} _ /.

  Section m.
    Context {m:Type -> Type}.

    Section m_Eq.
      Context `{! F_EqDec m ,! F_Eq_RDC m }.

      Section Eq.
        Context {A} `{! EqDec A ,! Eq_RDC A }.

        Local Instance _EqDec : EqDec (T m A) := { eq_dec := eq_dec `on` to }.
        Local Instance _Eq_RDC : Eq_RDC (T m A) := Deriving_Eq_RDC to eq_refl.
      End Eq.
      Global Instance _F_EqDec : F_EqDec (T m) := { f_eq_dec := @_EqDec }.
      Global Instance _F_Eq_RDC : F_Eq_RDC (T m) := { f_eq_rdc := @_Eq_RDC }.
    End m_Eq.

    Section m_Eqv.
      Context `{! F_Eqv m ,! F_EqvDec m ,! F_Eqv_RDC m }.

      Section Eqv.
        Context {A} `{! Eqv A ,! EqvDec A ,! Eqv_RDC A }.

        Local Instance _Eqv : Eqv (T m A) := { eqv := eqv `on` to }.
        Global Instance _IR_to_eqv : InjectionRespect (T m A) (U m A) to eqv eqv :=
          Deriving_IR to eqv eqv eq_refl.
        Local Instance _EqvDec : EqvDec (T m A) := { eqv_dec := eqv_dec `on` to }.
        Local Instance _Eqv_RDC : Eqv_RDC (T m A) :=
          { eqv_rdc := Deriving_RDC to eqv eqv_dec eqv eqv_dec eq_refl }.
      End Eqv.
      Global Instance _F_Eqv : F_Eqv (T m) := { f_eqv := @_Eqv }.
      Global Instance _F_EqvDec : F_EqvDec (T m) := { f_eqv_dec := @_EqvDec }.
      Global Instance _F_Eqv_RDC : F_Eqv_RDC (T m) := { f_eqv_rdc := @_Eqv_RDC }.
    End m_Eqv.

    Section m_PER_WF.
      Context `{! F_Eqv m ,! F_PER_WF m }.

      Section PER_WF.
        Context {A} `{! Eqv A ,! PER_WF A }.

        Local Instance _PER_WF : PER_WF (T m A) := Deriving_PER_WF to.
        Global Instance _IR_from_eqv_PER : InjectionRespect (U m A) (T m A) from eqv eqv :=
          Deriving_IR_inv to from eqv (eqv (T:=T m A)) eq_refl.
      End PER_WF.
      Global Instance _F_PER_WF : F_PER_WF (T m) := { f_per_wf := @_PER_WF }.
    End m_PER_WF.

    Section m_ER_WF.
      Context `{! F_Eqv m ,! F_ER_WF m }.

      Section ER_WF.
        Context {A} `{! Eqv A ,! ER_WF A }.

        Local Instance _ER_WF : ER_WF (T m A) := Deriving_ER_WF to.
        Global Instance _IR_from_eqv_ER : InjectionRespect (U m A) (T m A) from eqv eqv :=
          Deriving_IR_inv to from eqv (eqv (T:=T m A)) eq_refl.
        Global Instance _II_from_eqv_ER : InjectionInverse (U m A) (T m A) from to eqv :=
          Deriving_II_ext from to eq eqv.
      End ER_WF.
      Global Instance _F_ER_WF : F_ER_WF (T m) := { f_er_wf := @_ER_WF }.
    End m_ER_WF.

    Section m_PreOrd.
      Context `{! F_Lte m ,! F_PreOrd m ,! F_LteDec m ,! F_Lte_RDC m }.

      Section PreOrd.
        Context {A} `{! Lte A ,! PreOrd A ,! LteDec A ,! Lte_RDC A}.

        Local Instance _Lte : Lte (T m A) := { lte := lte `on` to }.
        Global Instance _IR_to_lte : InjectionRespect (T m A) (U m A) to lte lte :=
          Deriving_IR to lte lte eq_refl.
        Local Instance _PreOrd : PreOrd (T m A) := Deriving_PreOrd to.
        Local Instance _LteDec : LteDec (T m A) := { lte_dec := lte_dec `on` to }.
        Local Instance _Lte_RDC : Lte_RDC (T m A) := Deriving_Lte_RDC to eq_refl.
      End PreOrd.
      Global Instance _F_Lte : F_Lte (T m) := { f_lte := @_Lte }.
      Global Instance _F_PreOrd : F_PreOrd (T m) := { f_pre_ord := @_PreOrd }.
      Global Instance _F_LteDec : F_LteDec (T m) := { f_lte_dec := @_LteDec }.
      Global Instance _F_Lte_RDC : F_Lte_RDC (T m) := { f_lte_rdc := @_Lte_RDC }.
    End m_PreOrd.

    Section m_PartialOrd.
      Context `{! F_Lte m ,! F_Eqv m ,! F_ER_WF m ,! F_PartialOrd m ,! F_PartialOrdDec m ,! F_PartialOrd_RDC m }.

      Section PartialOrd.
        Context {A} `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! PartialOrdDec A ,! PartialOrd_RDC A }.

        Local Instance _PartialOrd : PartialOrd (T m A).
        eapply (Deriving_PartialOrd to).
        Grab Existential Variables.
        eapply _PreOrd.
        Grab Existential Variables.
        apply 
        Local Instance _PartialOrdDec : PartialOrdDec (T m A) := { pord_dec := pord_dec `on` to }.
        Local Instance _PartialOrd_RDC : PartialOrd_RDC (T m A) :=
          Deriving_PartialOrd_RDC (to:T m A -> U m A) eq_refl.
      End PartialOrd.
      Global Instance _Bif_PartialOrd : Bif_PartialOrd T := { bif_partial_ord := @_PartialOrd }.
      Global Instance _Bif_PartialOrdDec : Bif_PartialOrdDec T := { bif_partial_ord_dec := @_PartialOrdDec }.
      Global Instance _Bif_PartialOrd_RDC : Bif_PartialOrd_RDC T := { bif_partial_ord_rdc := @_PartialOrd_RDC }.
    End m_PartialOrd.

    Section TotalOrd.
      Context {m A}
        `{! Lte m ,! Eqv m ,! ER_WF m ,! TotalOrd m ,! TotalOrdDec m ,! TotalOrd_RDC m
         ,! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! TotalOrdDec A ,! TotalOrd_RDC A
         }.

      Local Instance _TotalOrd : TotalOrd (T m A) := Deriving_TotalOrd to.
      Local Instance _TotalOrdDec : TotalOrdDec (T m A) := { tord_dec := tord_dec `on` to }.
      Local Instance _TotalOrd_RDC : TotalOrd_RDC (T m A) :=
        Deriving_TotalOrd_RDC (to:T m A -> U m A) eq_refl.
    End TotalOrd.
    Global Instance _Bif_TotalOrd : Bif_TotalOrd T := { bif_total_ord := @_TotalOrd }.
    Global Instance _Bif_TotalOrdDec : Bif_TotalOrdDec T := { bif_total_ord_dec := @_TotalOrdDec }.
    Global Instance _Bif_TotalOrd_RDC : Bif_TotalOrd_RDC T := { bif_total_ord_rdc := @_TotalOrd_RDC }.

    Section Lattice.
      Context {m A}
        `{! Lte m ,! Eqv m ,! ER_WF m ,! PartialOrd m
         ,! Lattice m ,! BoundedLattice m ,! LatticeWF m ,! BoundedLatticeWF m
         ,! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A
         ,! Lattice A ,! BoundedLattice A ,! LatticeWF A ,! BoundedLatticeWF A
         }.
      Local Instance _Lattice : Lattice (T m A) :=
        { lmeet := from '.:' (lmeet `on` to)
        ; ljoin := from '.:' (ljoin `on` to)
        }.
      Global Instance _ID_lmeet_eq : InjectionDistribute (T m A) (U m A) to lmeet lmeet eq :=
        Deriving_ID to from lmeet lmeet eq eq_refl.
      Global Instance _ID_lmeet_eqv : InjectionDistribute (T m A) (U m A) to lmeet lmeet eqv :=
        Deriving_ID_ext to lmeet lmeet eq eqv.
      Global Instance _ID_ljoin_eq : InjectionDistribute (T m A) (U m A) to ljoin ljoin eq :=
        Deriving_ID to from ljoin ljoin eq eq_refl.
      Global Instance _ID_ljoin_eqv : InjectionDistribute (T m A) (U m A) to ljoin ljoin eqv :=
        Deriving_ID_ext to ljoin ljoin eq eqv.
      Local Instance _LatticeWF : LatticeWF (T m A) := Deriving_LatticeWF to.

      Local Instance _BoundedLattice : BoundedLattice (T m A) :=
        { ltop := from ltop
        ; lbot := from lbot
        }.
      Local Instance _BoundedLatticeWF : BoundedLatticeWF (T m A) :=
        Deriving_BoundedLatticeWF (to:T m A -> U m A) from eq_refl eq_refl.
    End Lattice.
    Global Instance _Bif_Lattice : Bif_Lattice T := { bif_lattice := @_Lattice }.
    Global Instance _Bif_LatticeWF : Bif_LatticeWF T := { bif_lattice_wf := @_LatticeWF }.
    Global Instance _Bif_BoundedLattice : Bif_BoundedLattice T := { bif_bounded_lattice := @_BoundedLattice }.
    Global Instance _Bif_BoundedLatticeWF : Bif_BoundedLatticeWF T := { bif_bounded_lattice_wf := @_BoundedLatticeWF }.
  End m.
End DerivingEverything_Bifunctor.
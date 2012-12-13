Require Import FP.Data.TwoThreeTrees.
Require Import FP.Structures.WellFormed.
Require Import FP.Data.N.
Require Import FP.Data.Ext.
Require Import FP.Structures.Peano.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Ord.
Require Import FP.Structures.Additive.

Import OrdNotation.
Import AdditiveNotation.


Module TwoThreeTreesWF.
  Import TwoThreeTrees.

  Inductive tree_iwf {K V} {Lat:Lattice K} {O:Ord K}
      : ext_top_bot K -> ext_top_bot K -> N -> tree K V -> Prop :=
    | NullWF : forall t_lower_bound t_upper_bound,
                 tree_iwf t_lower_bound t_upper_bound 0 Null_t
    | TwoWF : forall tl_lower_bound tl_upper_bound
                     tr_lower_bound tr_upper_bound
                     t_height
                     tl km vm tr,
                tree_iwf tl_lower_bound tl_upper_bound t_height tl
             -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
             -> tl_upper_bound < inject km < tr_lower_bound
             -> tree_iwf tl_lower_bound tr_upper_bound
                         (t_height+1)
                         (Two_t tl (km,vm) tr)
    | ThreeWF : forall tl_lower_bound tl_upper_bound
                       tm_lower_bound tm_upper_bound
                       tr_lower_bound tr_upper_bound
                       t_height
                       tl kl vl tm kr vr tr,
                  tree_iwf tl_lower_bound tl_upper_bound t_height tl
               -> tree_iwf tm_lower_bound tm_upper_bound t_height tm
               -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
               -> tl_upper_bound < inject kl < tm_lower_bound
               -> tm_upper_bound < inject kr < tr_lower_bound
               -> tree_iwf tl_lower_bound tr_upper_bound
                           (t_height+1)
                           (Three_t tl (kl,vl) tm (kr,vr) tr).

  Definition tree_wf {K V} {Lat:Lattice K} {O:Ord K} (t:tree K V) : Prop :=
    exists n:N, tree_iwf lbot ltop n t.

  Global Instance tree_WellFormed {K V} {Lat:Lattice K} {O:Ord K}
    : WellFormed (tree K V) := { wf := tree_wf }.

  Section wf.
    Context {K} {KOrd:OrdDec K} {KO:Ord K} {KLat:Lattice K} {LWF:LatticeWF K}.
    Context {V:Type}.

    Definition empty_wf : with_wf (tree K V).
      refine(
        ex_intro _ empty _
      ).
      simpl.
      exists 0.
      econstructor.
    Defined.

    Definition singleton_wf (k:K) (v:V) : with_wf (tree K V).
      refine(
        ex_intro _ (singleton k v) _
      ).
      simpl.
      exists (0+1).
      eapply (TwoWF _ lbot ltop _).
      econstructor.
      econstructor.
      eauto.

        
  End wf.

End TwoThreeTreesWF.


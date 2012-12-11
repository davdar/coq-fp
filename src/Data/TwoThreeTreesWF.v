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

Import TwoThreeTrees.

Inductive two_three_trees_iwf {K V} {Lat:Lattice K} {O:Ord K}
    : ext_top_bot K -> ext_top_bot K -> N -> tree K V -> Prop :=
  | NullWF : forall t_lower_bound t_upper_bound,
               two_three_trees_iwf t_lower_bound t_upper_bound 0 Null_t
  | TwoWF : forall tl_lower_bound tl_upper_bound
                   tr_lower_bound tr_upper_bound
                   t_height
                   tl km vm tr,
              two_three_trees_iwf tl_lower_bound tl_upper_bound t_height tl
           -> two_three_trees_iwf tr_lower_bound tr_upper_bound t_height tr
           -> tl_upper_bound < inject km < tr_lower_bound
           -> two_three_trees_iwf tl_lower_bound tr_upper_bound
                                  (t_height+1)
                                  (Two_t tl (km,vm) tr)
  | ThreeWF : forall tl_lower_bound tl_upper_bound
                     tm_lower_bound tm_upper_bound
                     tr_lower_bound tr_upper_bound
                     t_height
                     tl kl vl tm kr vr tr,
                two_three_trees_iwf tl_lower_bound tl_upper_bound t_height tl
             -> two_three_trees_iwf tm_lower_bound tm_upper_bound t_height tm
             -> two_three_trees_iwf tr_lower_bound tr_upper_bound t_height tr
             -> tl_upper_bound < inject kl < tm_lower_bound
             -> tm_upper_bound < inject kr < tr_lower_bound
             -> two_three_trees_iwf tl_lower_bound tr_upper_bound
                                    (t_height+1)
                                    (Three_t tl (kl,vl) tm (kr,vr) tr).
                
Definition two_three_trees_wf {K V} {Lat:Lattice K} {O:Ord K} (t:tree K V) : Prop :=
  exists n:N, two_three_trees_iwf lbot ltop n t.
                
  
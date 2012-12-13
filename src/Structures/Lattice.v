Require Import FP.Structures.Ord.
Require Import FP.Data.Function.

Import OrdNotation.
Import FunctionNotation.

Class Lattice T :=
  { lattice_OrdDec :> OrdDec T
  ; lmeet : T -> T -> T
  ; ljoin : T -> T -> T
  }.

Module LatticeNotation.
  Infix "/\" := lmeet.
  Infix "\/" := ljoin.
End LatticeNotation.
Import LatticeNotation.

Class LatticeWF T {O:Ord T} {L:Lattice T} :=
  { lattic_wf_OrdWF :> OrdWF T
  ; lmeet_ineq : forall t1 t2, ((t1 /\ t2) <= t1) `and` ((t1 /\ t2) <= t2)
  ; ljoin_ineq : forall t1 t2, (t1 <= (t1 \/ t2)) `and` (t2 <= (t1 \/ t2))
  }.

Class BoundedLattice T :=
  { bounded_lattice_Lattice :> Lattice T
  ; ltop : T
  ; lbot : T
  }.

Class BoundedLatticeWF T {O:Ord T} {L:BoundedLattice T} :=
  { ltop_ineq : forall t, t <= ltop
  ; lbot_ineq : forall t, lbot <= t
  }.

Definition lmin {t} {L:Lattice t} : t -> t -> t := lmeet.
Definition lmax {t} {L:Lattice t} : t -> t -> t := ljoin.

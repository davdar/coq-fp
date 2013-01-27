Require Import FP.Structures.Ord.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Eqv.
Require Import FP.Data.Function.

Import OrdNotation.
Import FunctionNotation.
Import EqvNotation.

Class Lattice T :=
  { lmeet : T -> T -> T
  ; ljoin : T -> T -> T
  }.
Arguments lmeet {T Lattice} _ _ : simpl never.
Arguments ljoin {T Lattice} _ _ : simpl never.

Module LatticeNotation.
  Infix "/\" := lmeet.
  Infix "\/" := ljoin.
End LatticeNotation.
Import LatticeNotation.

Class LatticeWF T {E:Eqv T} {O:Ord T} {L:Lattice T} :=
  { lmeet_ineq : forall t1 t2, ((t1 /\ t2) <= t1) `and` ((t1 /\ t2) <= t2)
  ; ljoin_ineq : forall t1 t2, (t1 <= (t1 \/ t2)) `and` (t2 <= (t1 \/ t2))
  }.

Class BoundedLattice T :=
  { bounded_lattice_Lattice :> Lattice T
  ; ltop : T
  ; lbot : T
  }.
Arguments ltop {T BoundedLattice} : simpl never.
Arguments lbot {T BoundedLattice} : simpl never.

Class BoundedLatticeWF T {E:Eqv T} {O:Ord T} {L:Lattice T} {BL:BoundedLattice T} :=
  { ltop_ineq : forall t, t <= ltop
  ; lbot_ineq : forall t, lbot <= t
  }.

Definition lmin {t} {L:Lattice t} : t -> t -> t := lmeet.
Definition lmax {t} {L:Lattice t} : t -> t -> t := ljoin.

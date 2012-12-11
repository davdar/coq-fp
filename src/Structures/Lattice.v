Require Import FP.Structures.Ord.

Class Lattice T :=
  { lattice_OrdDec :> OrdDec T
  ; lmeet : T -> T -> T
  ; ljoin : T -> T -> T
  }.

Class BoundedLattice T :=
  { bounded_lattice_Lattice :> Lattice T
  ; ltop : T
  ; lbot : T
  }.

Definition lmin {t} {L:Lattice t} : t -> t -> t := lmeet.
Definition lmax {t} {L:Lattice t} : t -> t -> t := ljoin.

Module LatticeNotation.
  Infix "/\" := lmeet.
  Infix "\/" := ljoin.
End LatticeNotation.
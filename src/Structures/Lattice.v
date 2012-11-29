Require Import FP.Structures.Ord.

Class Lattice t :=
  { lattice_OrdDec :> OrdDec t
  ; lmeet : t -> t -> t
  ; ljoin : t -> t -> t
  }.

Definition lmin {t} {L:Lattice t} : t -> t -> t := lmeet.
Definition lmax {t} {L:Lattice t} : t -> t -> t := ljoin.
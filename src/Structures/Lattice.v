Require Import Structures.Ord.

Class Lattice t :=
  { lattice_Ord :> Ord t
  ; meet : t -> t -> t
  ; join : t -> t -> t
  }.

Definition min {t} {L:Lattice t} : t -> t -> t := meet.
Definition max {t} {L:Lattice t} : t -> t -> t := join.
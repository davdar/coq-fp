Require Import FP.CoreClasses.
Require Import FP.Classes.

Instance Prop_Plus : Plus Prop := { plus := or }.
Instance Prop_Zero : Zero Prop := { zero := False }.
Instance Prop_Times : Times Prop := { times := and }.
Instance Prop_One : One Prop := { one := True }.
Instance Prop_Lattice : Lattice Prop :=
  { ljoin := or
  ; lmeet := and
  }.
Instance Prop_BoundedLattice : BoundedLattice Prop :=
  { lbot := False
  ; ltop := True
  }.

Instance Set_Plus : Plus Set := { plus := sum }.
Instance Set_Zero : Zero Set := { zero := Empty_set }.
Instance Set_Times : Times Set := { times := prod }.
Instance Set_One : One Set := { one := unit }.
Instance Set_Lattice : Lattice Set :=
  { ljoin := sum
  ; lmeet := prod
  }.
Instance Set_BoundedLattice : BoundedLattice Set :=
  { lbot := Empty_set
  ; ltop := unit
  }.

Instance Type_Plus : Plus Type := { plus := sum }.
Instance Type_Zero : Zero Type := { zero := Empty_set }.
Instance Type_Times : Times Type := { times := prod }.
Instance Type_one : One Type := { one := unit }.
Instance Type_Lattice : Lattice Type :=
  { ljoin := sum
  ; lmeet := prod
  }.
Instance Type_BoundedLattice : BoundedLattice Type :=
  { lbot := Empty_set
  ; ltop := unit
  }.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Multiplicative.
Require Import FP.Data.Sum.
Require Import FP.Data.Prod.

Section Type_sum_Monoid.
  Definition sum_Set_Monoid : Monoid Set :=
    {| monoid_times := (sum:Set -> Set -> Set)
     ; monoid_unit := Empty_set
    |}.
  Definition sum_Type_Monoid : Monoid Type :=
    {| monoid_times := sum
     ; monoid_unit := (Empty_set:Type)
    |}.
End Type_sum_Monoid.

Section Type_prod_Monoid.
  Definition prod_Set_Monoid : Monoid Set :=
    {| monoid_times := (prod:Set -> Set -> Set)
     ; monoid_unit := unit
    |}.
  Definition prod_Type_Monoid : Monoid Type :=
    {| monoid_times := prod
     ; monoid_unit := (unit:Type)
    |}.
End Type_prod_Monoid.

Instance Additive_Type : Additive Type :=
  { additive_Monoid := sum_Type_Monoid }.
Instance Multiplicative_Type : Multiplicative Type :=
  { multiplicative_Monoid := prod_Type_Monoid }.
Instance Additive_Set : Additive Set :=
  { additive_Monoid := sum_Set_Monoid }.
Instance Multiplicative_Set : Multiplicative Set :=
  { multiplicative_Monoid := prod_Set_Monoid }.
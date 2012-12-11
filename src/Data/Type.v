Require Import FP.Structures.Additive.
Require Import FP.Structures.Multiplicative.
Require Import FP.Data.Sum.
Require Import FP.Data.Prod.

Instance Additive_Type : Additive Type :=
  { additive_Monoid := sum_Type_Monoid }.
Instance Multiplicative_Type : Multiplicative Type :=
  { multiplicative_Monoid := prod_Type_Monoid }.
Instance Additive_Set : Additive Set :=
  { additive_Monoid := sum_Set_Monoid }.
Instance Multiplicative_Set : Multiplicative Set :=
  { multiplicative_Monoid := prod_Set_Monoid }.
Require Import Structures.Additive.
Require Import Structures.Multiplicative.
Require Import Data.Sum.
Require Import Data.Prod.

Instance Additive_Type : Additive Type :=
  { Additive_Monoid := sum_Type_Monoid }.

Instance Multiplicative_Type : Multiplicative Type :=
  { Multiplicative_Monoid := prod_Type_Monoid }.
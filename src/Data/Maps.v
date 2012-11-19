Require Import Data.TwoThreeTrees.
Require Import Data.UoAssoc.

Definition omap K V := two3map K V.
Definition umap K V := uo_assoc_map K V.

Definition oset A := two3set A.
Definition uset A := uo_assoc_set A.

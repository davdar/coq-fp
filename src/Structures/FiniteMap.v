Require Import Structures.Pointed.

Class FiniteMap T :=
{ finite_map_Pointed :> forall {K V}, Pointed (T K V)
; lookup : forall {K V}, K -> T K V -> option V
; insert : forall {K V}, K -> V -> T K V -> T K V
; delete : forall {K V}, K -> T K V -> T K V
; update : forall {K V}, K -> (V -> V) -> T K V -> T K V
}.

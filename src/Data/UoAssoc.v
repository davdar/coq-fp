Inductive uo_assoc_map K V := UoAssocMap { un_uo_assoc_map : list (K*V) }.

Section Monad.
End Monad.

Definition uo_assoc_set A := uo_assoc_map A unit.

Definition uo_assoc_multimap K V := list (K*V).
Definition uo_assoc_multiset := list.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.

Open Scope signature_scope.

Definition respectful_iff {A B}
    (R1:A -> A -> Prop) (R2:B -> B -> Prop) (f:A -> B) (g:A -> B) : Prop :=
    forall x y, R1 x y <-> R2 (f x) (g y).
Definition respectful_follows {A B}
    (R1:A -> A -> Prop) (R2:B -> B -> Prop) (f:A -> B) (g:A -> B) : Prop :=
    forall x y, R2 (f x) (g y) -> R1 x y.
Infix "<==>" := respectful_iff (at level 55, right associativity).
Infix "<==" := respectful_follows (at level 55, right associativity).
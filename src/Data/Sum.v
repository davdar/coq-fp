Require Export Init.Datatypes.

Open Scope type_scope.

Definition collapse {A} (a:A+A) : A := match a with inl x => x | inr x => x end.

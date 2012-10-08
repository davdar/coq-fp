Require Import Data.String.
Require Import Structures.Monoid.

Inductive string_builder := StringBuilder { un_string_builder : string -> string }.

Definition run_string_builder sb := un_string_builder sb EmptyString.

Instance string_builder_Monoid : Monoid string_builder.
Admitted.
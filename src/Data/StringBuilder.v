Require Import FP.Data.String.
Require Import FP.Structures.Monoid.
Require Import FP.Data.Function.

Import FunctionNotation.
Import MonoidNotation.

Inductive string_builder := StringBuilder { un_string_builder : string -> string }.

Definition run_string_builder sb := un_string_builder sb EmptyString.
Definition mk_string_builder s := StringBuilder $ fun tl => s ** tl.

Definition string_builder_append (b1:string_builder) (b2:string_builder) : string_builder :=
  StringBuilder $ fun s => un_string_builder b1 (un_string_builder b2 s).

Instance string_builder_Semigroup : Semigroup string_builder :=
  { gtimes := string_builder_append }.
Instance string_builder_Monoid : Monoid string_builder :=
  { gunit := mk_string_builder "" }.
Require Import FP.Data.String.
Require Import FP.Data.StringStructures.
Require Import FP.Structures.Monoid.
Require Import FP.Data.Function.

Import FunctionNotation.
Import MonoidNotation.
Import StringNotation.

Inductive string_builder := StringBuilder { un_string_builder : string -> string }.

Definition run_string_builder sb := un_string_builder sb EmptyString.
Definition mk_string_builder s := StringBuilder $ fun tl => s ** tl.

Definition string_builder_append (b1:string_builder) (b2:string_builder) : string_builder :=
  StringBuilder $ fun tl => un_string_builder b1 $ un_string_builder b2 tl.

Instance string_builder_Monoid : Monoid string_builder :=
  { monoid_times := string_builder_append
  ; monoid_unit := mk_string_builder ""
  }.
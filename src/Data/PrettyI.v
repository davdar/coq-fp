Require Import FP.Data.StringPre.
Require Import FP.Data.NPre.

Import StringNotation.

Inductive doc :=
  | NilD : doc
  | ConcatD : doc -> doc -> doc
  | TextD : string -> doc
  | NestD : N -> doc -> doc
  | LineD : doc
  | UnionD : doc -> doc -> doc.

Class Pretty t :=
  { pretty : t -> doc }.

Definition nil_d : doc := NilD.
Definition concat_d : doc -> doc -> doc := ConcatD.
Definition nest_d : N -> doc -> doc := NestD.
Definition text_d : string -> doc := TextD.
Definition line_d : doc := LineD.

Fixpoint flatten_d (d:doc) : doc :=
  match d with
  | NilD => NilD
  | ConcatD dl dr => ConcatD (flatten_d dl) (flatten_d dr)
  | NestD i dn => NestD i (flatten_d dn)
  | TextD s => TextD s
  | LineD => TextD " "
  | UnionD dl dr => flatten_d dl
  end.

Definition group_d (d:doc) : doc := UnionD (flatten_d d) d.


Require Import FP.Data.String.
Require Import FP.Data.N.

Import StringNotation.

Inductive doc :=
  | NilD : doc
  | ConcatD : doc -> doc -> doc
  | TextD : string -> doc
  | NestD : N -> doc -> doc
  | LineD : string -> doc
  | GroupD : doc -> doc.

Class Pretty t :=
  { pretty : t -> doc }.

Definition nil_d : doc := NilD.
Definition concat_d : doc -> doc -> doc := ConcatD.
Definition nest_d : N -> doc -> doc := NestD.
Definition text_d : string -> doc := TextD.
Definition line_d : doc := LineD " ".
Definition line_with_d : string -> doc := LineD.
Definition group_d := GroupD.
Require Export Coq.Strings.String.

Require Import Data.List.

Fixpoint string2list s :=
  match s with
  | EmptyString => nil
  | String c s' => c::string2list s'
  end.

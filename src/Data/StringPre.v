Require Coq.Strings.String.

Require Import FP.Data.AsciiPre.
Require Import FP.Data.Function.
Require Import FP.Data.ListPre.
Require Import FP.Structures.Convertible.

Import FunctionNotation.
Import ListNotation.

Module StringNotation.
  Open Scope string_scope.
End StringNotation.

Definition string := String.string.
Definition EmptyString := String.EmptyString.
Definition String := String.String.

Fixpoint string2list (s:string) : list ascii :=
  match s with
  | EmptyString => nil
  | String c s' => c :: string2list s'
  end.
Fixpoint list2string (l:list ascii) : string :=
  match l with
  | nil => EmptyString
  | x::l' => String x $ list2string l'
  end.
Instance string_list_Convertible : Convertible string (list ascii) :=
  { convert := string2list }.
Instance list_string_Convertible : Convertible (list ascii) string :=
  { convert := list2string }.


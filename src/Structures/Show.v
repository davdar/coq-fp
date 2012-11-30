Require Import FP.Data.AsciiPre.
Require Import FP.Data.StringPre.

Require Import FP.Structures.Injection.
Require Import FP.Structures.Monoid.

Import MonoidNotation.

Class ShowResult r :=
  { show_result_monoid :> Monoid r
  ; show_result_ascii_injection :> Injection ascii r
  }.
Hint Immediate Build_ShowResult : typeclass_instances.

Class Show t := { show : forall {r} {SR:ShowResult r}, t -> r }.

Section raw.
  Context {r} {SR:ShowResult r}.

  Definition raw_char : ascii -> r := inject.

  Fixpoint raw_string s :=
    match s with
    | EmptyString => gunit
    | String c s' => raw_char c ** raw_string s'
    end.
End raw.

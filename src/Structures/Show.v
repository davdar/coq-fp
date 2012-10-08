Require Import Data.Ascii.
Require Import Data.String.
Require Import Structures.Injection.
Require Import Structures.Monoid.
Require Import Structures.Pointed.

Import MonoidNotation.

Class ShowResult T :=
{ show_result_monoid : Monoid T
; show_result_ascii_morphism : Injection ascii T
}.
Hint Immediate Build_ShowResult : typeclass_instances.
Hint Immediate show_result_monoid : typeclass_instances.
Hint Immediate show_result_ascii_morphism : typeclass_instances.

Class Show T := { show : forall {R} {SR:ShowResult R}, T -> R }.

Section rawshow_string.
  Context {T} {SR:ShowResult T}.

  Definition rawshow_char : ascii -> T := inject.

  Fixpoint rawshow_string s :=
    match s with
    | EmptyString => top
    | String c s' => rawshow_char c ** rawshow_string s'
    end.
End rawshow_string.

Require Import Ascii.
Require Import String.

Require Import Morphism.
Require Import Monoid.
Import MonoidNotation.
Require Import Pointed.

Class ShowResult T :=
{ show_result_monoid : Monoid T
; show_result_ascii_morphism : Morphism ascii T
}.
Hint Immediate Build_ShowResult : typeclass_instances.
Hint Immediate show_result_monoid : typeclass_instances.
Hint Immediate show_result_ascii_morphism : typeclass_instances.

Class Show T := { show : forall {R} {SR:ShowResult R}, T -> R }.

Section rawshow_string.
  Context {T} {SR:ShowResult T}.

  Definition rawshow_char c := morph c.

  Fixpoint rawshow_string s :=
    match s with
    | EmptyString => top
    | String c s' => rawshow_char c ** rawshow_string s'
    end.
End rawshow_string.

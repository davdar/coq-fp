Require Import FP.Data.Function.
Require Import FP.Data.String.
Require Import FP.Data.Ascii.
Require Import FP.Data.N.
Require Import FP.Data.NStructures.
Require Import FP.Structures.Show.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Comonad.
Require Import FP.Structures.Foldable.
Require Import FP.Structures.Monad.
Require Import FP.Data.PrettyI.

Import MonoidNotation.
Import CharNotation.
Import ComonadNotation.
Import FunctionNotation.

Section Show.
  Section string_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition string_show (s:string) : R :=
         raw_char """"%char
      ** raw_string s
      ** raw_char """"%char.
  End string_show.

  Global Instance string_Show : Show string := { show := string_show }.
End Show.

Section Monoid.
  Global Instance string_Monoid : Monoid string :=
    { monoid_times := String.append
    ; monoid_unit := EmptyString
    }.
End Monoid.

Section Injection.
  Global Instance string_ascii_HasInjection : HasInjection ascii string :=
    { inject c := String c EmptyString }.
End Injection.

Section Foldable.
  Fixpoint string_cofold {w} {W:Comonad w} {B} (f:ascii -> w B -> B) (bW:w B) (t:string) : B :=
    match t with
    | EmptyString => coret bW
    | String a t =>
        let bW := codo bW => string_cofold f bW t
        in f a bW
    end.
  Global Instance string_Foldable : Foldable ascii string :=
    { cofold := @string_cofold }.
End Foldable.

Section Buildable.
  Definition string_mbuild {m} {M:Monad m} (f:forall {C}, (ascii -> C -> C) -> C -> m C) : m string :=
    f String EmptyString.
  Global Instance string_Buildable : Buildable ascii string :=
    { mbuild := @string_mbuild }.
End Buildable.

Instance N_Pretty : Pretty N := { pretty := text_d '.' show }.
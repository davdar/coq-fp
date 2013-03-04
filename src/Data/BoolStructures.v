Require Import FP.Structures.Show.
Require Import FP.Data.String.

Import StringNotation.

Section Show.
  Section bool_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition bool_show (x:bool) : R :=
      raw_string (if x then "true" else "false").
  End bool_show.

  Global Instance bool_Show : Show bool := { show := bool_show }.
End Show.
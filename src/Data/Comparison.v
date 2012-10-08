Require Import Structures.Lte.

Import LteNotation.

Inductive comparison := Lt | Eq | Gt.

Section comparison.
  Context {T} {L:LteDec T}.

  Definition compare (x:T) (y:T) : comparison :=
    if x '<=! y then
      if y '<=! x then Eq
      else Lt
    else Gt.
End comparison.
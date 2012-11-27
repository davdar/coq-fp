Require Import FP.Data.Lens.

Class HasLens A S :=
  { get_lens : lens A S }.
Arguments get_lens {A} S {HasLens}.
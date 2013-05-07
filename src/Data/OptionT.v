Require Import FP.Data.ErrorT.

Definition OptionT m A := ErrorT unit m A.
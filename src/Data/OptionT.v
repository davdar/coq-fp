Require Import FP.Data.ErrorT.

Definition option_t m A := error_t unit m A.
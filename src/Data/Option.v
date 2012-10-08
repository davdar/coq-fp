Require Export Coq.Init.Datatypes.

Inductive option_t m (A:Type) := OptionT { un_option_t : option (m A) }.

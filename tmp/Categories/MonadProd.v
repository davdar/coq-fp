(* meaningless *)
Class MonadProd m :=
  { munit : forall {A}, m A
  ; mtimes : forall {A B}, m A -> m B -> m (A*B)
  }.
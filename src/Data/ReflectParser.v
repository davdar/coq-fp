Require Import Data.String.
Require Import Data.Ascii.
Require Import Data.Maps.
Require Import Structures.MapI.

Import StringNotation.

Inductive parser_type :=
  | Unit_t : parser_type
  | Sum_t : parser_type -> parser_type -> parser_type
  | Prod_t : parser_type -> parser_type -> parser_type.

Fixpoint reflect (t:parser_type) : Type :=
  match t with
  | Unit_t => unit
  | Sum_t a b => reflect a + reflect b
  | Prod_t a b => reflect a * reflect b
  end%type.

Definition In {K V} : K -> omap K V -> Prop. Admitted.
Definition in_lookup {K V} : forall k (m:omap K V) (p:In k m), V. Admitted.

Inductive parser : omap string parser_type -> parser_type -> Type :=
  | Emp : forall G A, parser G A
  | Eps : forall G A, reflect A -> parser G A
  | Lit : forall G, ascii -> parser G Unit_t
  | Alt : forall G A B, parser G A -> parser G B -> parser G (Sum_t A B)
  | Con : forall G A B, parser G A -> parser G B -> parser G (Prod_t A B)
  | Var : forall G (x:string) (p:In x G), parser G (in_lookup x G p)
  | Fix : forall G A, parser (minsertl "x" A G) A -> parser G A.

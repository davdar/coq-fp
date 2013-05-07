(*
Require Import Structures.Ord.
Require Import Structures.Eqv.
Require Import Data.Maps.
Require Import Data.Function.
Require Import Structures.FiniteMap.

Import FunctionNotation.
Import EqvNotation.

Section grammar.
  Variable T:Type.
  Context {TO:Ord T}.
  Context {E:EqvDec T}.

  CoInductive grammar : Type -> Type :=
    | Emp_g : forall {A}, grammar A
    | Eps_g : forall {A}, oset A -> grammar A
    | Lit_g : T -> grammar T
    | Alt_g : forall {A}, grammar A -> grammar A -> grammar A
    | Con_g : forall {A B}, grammar A -> grammar B -> grammar (A*B)
    | Null_g : forall {A}, grammar A -> grammar A
    | Map_g : forall {A B}, (A -> B) -> grammar A -> grammar B
    .

  CoFixpoint deriv {A} (t:T) (g:grammar A) : grammar A :=
    match g with
    | Emp_g _ => Emp_g
    | Eps_g _ o => Emp_g
    | Lit_g t' => if t ~=! t' then Eps_g (singleton t tt) else Emp_g
    | Alt_g _ gl gr => Alt_g (deriv t gl) (deriv t gr)
    | Con_g _ _ gl gr =>
        Alt_g (Con_g (deriv t gl) gr)
              (Con_g (Null_g gl) (deriv t gr))
    | Null_g _ _ => Emp_g
    | Map_g _ _ f g => Map_g f (deriv t g)
    end.

  Definition set_union {A} : oset A -> oset A -> oset A.
  Admitted.
  Definition set_product {A B} : oset A -> oset B -> oset (A*B).
  Admitted.
  Definition set_map {A B} : (A -> B) -> oset A -> oset B.
  Admitted.

  CoFixpoint compact {A} (g:grammar A) : grammar A :=
    match g in grammar A' return grammar A' with
    | Emp_g _ => Emp_g
    | Eps_g _ o => Eps_g o
    | Lit_g t => Lit_g t
    | Alt_g _ gl gr =>
        match gl in grammar A' return grammar A' -> grammar A' with
        (* emp | gr => gr *)
        | Emp_g _ => fun gr => gr
        | Eps_g _ ol => fun gr =>
            match gr in grammar A' return oset A' -> grammar A' with
            (* eps | eps => eps *)
            | Eps_g _ or => fun ol => Eps_g (set_union ol or)
            (* eps | gr => eps | gr *)
            | gr => fun ol => Alt_g (Eps_g ol) gr
            end ol
        | gl => fun gr =>
            match gr in grammar A' return grammar A' -> grammar A' with
            (* gl | emp => gl *)
            | Emp_g _ => fun gl => gl
            (* gl | gr => gl | gr *)
            | gr => fun gl => Alt_g gl gr
            end gl
        end gr
    | Con_g _ _ gl gr =>
        match gl in grammar A', gr in grammar B' return grammar (A'*B') with
        (* emp ~ _ => emp *)
        | Emp_g _, _ => Emp_g
        (* _ ~ emp => emp *)
        | _, Emp_g _ => Emp_g
        (* eps ~ eps => eps *)
        | Eps_g _ ol, Eps_g _ or => Eps_g (set_product ol or)
        (* gl ~ gr => gl ~ gr *)
        | gl, gr => Con_g gl gr
        end
    | Null_g _ g' =>
        match g' in grammar A' return grammar A' with
        (* null emp => emp *)
        | Emp_g _ => Emp_g
        (* null eps => eps *)
        | Eps_g _ o => Eps_g o
        (* null lit => emp *)
        | Lit_g _ => Emp_g
        (* null (gl | gr) => null gl | null gr *)
        | Alt_g _ gl gr => Alt_g (Null_g gl) (Null_g gr)
        (* null (gl ~ gr) => null gl ~ null gr *)
        | Con_g _ _ gl gr => Con_g (Null_g gl) (Null_g gr)
        (* null (null g) => null g *)
        | Null_g _ g'' => Null_g g''
        (* null (g @ f) => null g @ f *)
        | Map_g _ _ f g'' => Map_g f (Null_g g'')
        end
    | Map_g _A _B f g' =>
      match g' in grammar A' return (A' -> _B) -> grammar _B with
      (* emp @ f ==> emp *)
      | Emp_g _ => fun _ => Emp_g
      (* eps o @ f ==> eps (map f o) *)
      | Eps_g _ o => fun f => Eps_g (set_map f o)
      (* g'' @ f => g'' @ f *)
      | g'' => fun f => Map_g f g''
      end f
    end.

  Fixpoint compact_n {A} (n:nat) : grammar A -> grammar A :=
    match n with
    | O => id
    | S n' => compact_n n' <.> compact
    end.

  Fixpoint extract_n {A} (n:nat) (g:grammar A) {struct n} : option (oset A) :=
    match n, g in grammar T' return option (oset T') with
    | _, Eps_g _ o => Some o
    | O, _ => None
    | S n', g => extract_n n' (compact g)
    end.

  Definition optimize {A} : grammar A -> grammar A := compact_n 20.

  Fixpoint parse {A} input g : option (oset A) :=
    match input with
    | nil => extract_n 1000 (Null_g g)
    | cons x xs => parse xs (optimize (deriv x g))
    end.
End grammar.
Arguments Emp_g {T A}.
Arguments Eps_g {T A} _.
Arguments Lit_g {T} _.
Arguments Alt_g {T A} _ _.
Arguments Con_g {T A B} _ _.
Arguments Null_g {T A} _.
Arguments Map_g {T A B} _ _.
Arguments compact_n {T A} _ _.
Arguments extract_n {T A} _ _.
Arguments optimize {T A} _.
Arguments parse {T E A} _ _.

Require Import Ascii.
Require Import String.
Require Import List.
Open Scope char.

CoFixpoint xs := Alt_g (Eps_g (singleton nil tt))
                       (Map_g (fun (p:ascii*list ascii) => let (x,y) := p in cons x y)
                              (Con_g (Lit_g "x"%char)
                                     xs)).

Fixpoint string2list s :=
  match s with
  | EmptyString => nil
  | String a s' => a::string2list s'
  end.

Definition input := string2list "".

(*
Eval compute in parse input xs.
*)

Definition foo := Null_g xs.

(*
Eval compute in (compact_n 1 foo).
*)
*)

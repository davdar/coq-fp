Require Import FP.Data.String.
Require Import FP.Data.N.
Require Import FP.Data.Z.
Require Import FP.Structures.Monoid.
Require Import FP.Data.Function.
Require Import FP.Data.List.
Require Import FP.Data.Ascii.
Require Import FP.Structures.Convertible.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Ord.
Require Import FP.Structures.Foldable.
Require Import FP.Data.List.
Require Import FP.Data.Fuel.
Require Import FP.Data.Susp.
Require Import FP.Structures.MonadFix.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Applicative.
Require Import FP.Structures.Monad.
Require Import FP.Data.Option.
Require Import FP.Data.PrettyI.

Import SuspNotation.
Import MonadNotation.
Import ApplicativeNotation.
Import FunctorNotation.
Import ZNotation.
Import CharNotation.
Import ListNotation.
Import MonoidNotation.
Import FunctionNotation.
Import AdditiveNotation.
Import OrdNotation.

Inductive tinydoc :=
  | NilTD : tinydoc
  | ConcatTD : string -> tinydoc -> tinydoc
  | LineTD : N -> tinydoc -> tinydoc.

Fixpoint layout' (td:tinydoc) : (string->string) -> string :=
  match td with
  | NilTD => fun k => k ""
  | ConcatTD s td => fun k => layout' td (fun s2 => k (s ** s2))
  | LineTD i td => fun k => layout' td (fun s => k (convert (to:=string) (newline :: replicate i " "%char) ** s))
  end.
Definition layout (td:tinydoc) : string := layout' td id.

Fixpoint fits (w:Z) (td:tinydoc) :=
  if w '<! 0%Z then
    false
  else
    match td with
    | NilTD => true
    | ConcatTD s td => fits (w - convert (length (convert s))) td
    | LineTD i td => true
    end.
Definition better (w:Z) (k:Z) (td1:susp tinydoc) (td2:susp tinydoc) : susp tinydoc :=
  let td1' := force td1 in
  if fits (w-k) td1' then
    delay | td1'
  else
    delay | force td2.

Definition be : Z -> Z -> list (N*doc) -> fuel (susp tinydoc) :=
  curry2 $
  mfix $ fun be args =>
    let be w k ds := be (w,k,ds) in
    let '(w,k,ds) := args in
    match ds with
    | [] => ret (delay | NilTD)
    | (i,NilD)::ds => be w k ds
    | (i,ConcatD dl dr)::ds => be w k ((i,dl)::(i,dr)::ds)
    | (i,NestD j dn)::ds => be w k ((i+j,dn)::ds)
    | (i,TextD s)::ds =>
        r <- be w (k+convert (length (convert s))) ds ;;
        ret (delay | ConcatTD s (force r))
    | (i,LineD)::ds =>
        r <- be w (convert i) ds ;;
        ret (delay | LineTD i (force r))
    | (i,UnionD dl dr)::ds =>
        fret (better w k) <@> (be w k ((i,dl)::ds)) <@> (be w k ((i,dr)::ds))
    end.

Definition best (w:Z) (k:Z) (d:doc) : fuel tinydoc := force <$> be w k [(0,d)].

Definition run_pretty' (w:N) (d:doc) : fuel string := layout <$> best (convert w) 0%Z d.
Definition run_pretty w d : option string := gtimes (convert [newline]) <$> run_fuel 100000 (run_pretty' w d).

(* example *)

Inductive tree := Node : string -> list tree -> tree.

Fixpoint show_tree (t:tree) : doc :=
  let map_show_trees :=
  fix map_show_trees ts :=
    match ts with
    | [] => []
    | t::ts => show_tree t::map_show_trees ts
    end
  in
  let show_trees :=
  fix show_trees t ts :=
    let tl :=
      match ts with
      | [] => nil_d
      | t::ts => text_d "," `concat_d` line_d `concat_d` show_trees t ts
      end
    in t `concat_d` tl
  in
  let show_bracket :=
  fix show_bracket ts :=
    match ts with
    | [] => nil_d
    | t::ts => text_d "[" `concat_d` nest_d 1 (show_trees t ts) `concat_d` text_d "]"
    end
  in
  let '(Node s ts) := t in
  group_d (text_d s `concat_d` nest_d (convert (length (convert s))) (show_bracket (map_show_trees ts))).

Definition t1 : tree :=
  Node "aaa" [Node "bbb" [Node "ccc" []; Node "ddd" []]; Node "eee" [Node "fff" []; Node "ggg" []]; Node "hhh" []].

(*
Eval compute in
  s <- run_pretty 20 (show_tree t1) ;;
  ret $ convert [newline] ** s.
*)
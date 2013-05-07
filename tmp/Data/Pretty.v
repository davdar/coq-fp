Require Import FP.Data.String.
Require Import FP.Data.N.
Require Import FP.Data.Z.
Require Import FP.Structures.Monoid.
Require Import FP.Data.Function.
Require Import FP.Data.List.
Require Import FP.Data.ListStructures.
Require Import FP.Data.GeneralizedList.
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
Require Import FP.Data.StringBuilder.

Import StringNotation.
Import NNotation.
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

Fixpoint layout (td:tinydoc) : string_builder :=
  match td with
  | NilTD => mk_string_builder ""
  | ConcatTD s td => mk_string_builder s ** layout td
  | LineTD i td => mk_string_builder (convert_to string (newline :: replicate i " "%char)) ** layout td
  end.
Inductive fmode :=
  | Flat
  | Break.

Definition fits : Z -> list (N*fmode*doc) -> fuel bool :=
  mfix2 $ fun fits w ps =>
    if w <! 0%Z then
      ret false
    else
      match ps with
      | [] => ret true
      | (_,_,NilD)::ps => fits w ps
      | (i,m,ConcatD dl dr)::ps => fits w ((i,m,dl)::(i,m,dr)::ps)
      | (i,m,NestD j dn)::ps => fits w ((i+j,m,dn)::ps)
      | (i,m,TextD s)::ps => fits (w - length s) ps
      | (i,Flat,LineD s)::ps => fits (w - length s) ps
      | (i,Break,LineD _)::_ => ret true
      | (i,m,GroupD dg)::ps => fits w ((i,Flat,dg)::ps)
      end.

Definition format : Z -> Z -> list (N*fmode*doc) -> fuel tinydoc :=
  curry $
  mfix2 $ fun format wk ps =>
    let format (w:Z) (k:Z) (ps:list (N*fmode*doc)) := format (w,k) ps in
    let '(w,k) := wk in
    match ps with
    | [] => ret NilTD
    | (i,m,NilD)::ps => format w k ps
    | (i,m,ConcatD dl dr)::ps => format w k ((i,m,dl)::(i,m,dr)::ps)
    | (i,m,NestD j dn)::ps => format w k ((i+j,m,dn)::ps)
    | (i,m,TextD s)::ps => ConcatTD s <$> format w (k + length s) ps
    | (i,Flat,LineD s)::ps => ConcatTD s <$> format w (k + length s) ps
    | (i,Break,LineD s)::ps => LineTD i <$> format w (convert i) ps
    | (i,m,GroupD dg)::ps =>
        b <- fits (w-k) ((i,Flat,dg)::ps) ;;
        if b then
          format w k ((i,Flat,dg)::ps)
        else
          format w k ((i,Break,dg)::ps)
   end.
    
Definition run_pretty (w:N) (d:doc) : option string :=
  let one_million := 1000000 in
  run_fuel one_million $ begin
    td <- format (convert w) 0%Z [(0,Flat,GroupD d)] ;;
    let nl := mk_string_builder $ convert [newline] in
    ret $ run_string_builder $ nl ** layout td ** nl
  end.

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
  s <- run_pretty 20 $ show_tree t1 ;;
  ret $ convert [newline] ** s.
*)
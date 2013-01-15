Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Injection.
Require Import FP.Data.Option.
Require Import FP.Structures.Ord.
Require Import FP.Data.Function.
Require Import FP.Data.Sum.
Require Import FP.Data.Unit.

Import FunctionNotation.
Import LatticeNotation.
Import OrdNotation.

Definition ext_bot := option.

Section ext_top.
  Inductive ext_top A := ExtTop { un_ext_top : option A }.
  Global Arguments ExtTop {A} _.
  Global Arguments un_ext_top {A} _.

  Definition ext_top_to_sum {A} (et:ext_top A) : A + unit :=
    match un_ext_top et with
    | None => inr tt
    | Some a => inl a
    end.

  Global Instance ext_top_Injection_sum {A} : Injection (ext_top A) (A + unit).

  Section EqDec.
    Context {A} {E:EqDec A}.

    Global Instance ext_top_EqDec : EqDec (ext_top A) :=
      { eq_dec := eq_dec `on` ext_top_to_sum }.
  End EqDec.

  Section Eqv.
    Context {A} {E:Eqv A}.

    Global Instance ext_top_Eqv : Eqv (ext_top A) :=
      { eqv := eqv `on` ext_top_to_sum }.
  End Eqv.

  Section EqvDec.
    Context {A} {E:EqvDec A}.

    Global Instance ext_top_EqvDec : EqvDec (ext_top A) :=
      { eqv_dec := eqv_dec `on` ext_top_to_sum }.
  End EqvDec.

  Section Ord.
    Context {A} {E:Ord A}.

    Global Instance ext_top_Ord : Ord (ext_top A) :=
      { lt := lt `on` ext_top_to_sum }.
  End Ord.

  Section OrdDec.
    Context {A} {O:OrdDec A}.

    Global Instance ext_top_OrdDec : OrdDec (ext_top A) :=
      { ord_dec := ord_dec `on` ext_top_to_sum }.
  End OrdDec.
End ext_top.

Section ext_top_bot.
  Inductive ext_top_bot A := ExtTopBot { un_ext_top_bot : option (option A) }.
  Global Arguments ExtTopBot {A} _.
  Global Arguments un_ext_top_bot {A} _.

  Global Instance ext_top_bot_Injection {A} : Injection A (ext_top_bot A) :=
    { inject := ExtTopBot '.' Some '.' Some }.

  Definition ext_top_bot_to_sum {A} (e:ext_top_bot A) : unit + A + unit :=
    match un_ext_top_bot e with
    | None => inr tt
    | Some None => inl (inl tt)
    | Some (Some a) => inl (inr a)
    end.

  Section EqDec.
    Context {A} {E:EqDec A}.

    Global Instance ext_top_bot_EqDec : EqDec (ext_top_bot A) :=
      { eq_dec := eq_dec `on` ext_top_bot_to_sum }.
  End EqDec.

  Section Eqv.
    Context {A} {E:Eqv A}.

    Global Instance ext_top_bot_Eqv : Eqv (ext_top_bot A) :=
      { eqv := eqv `on` ext_top_bot_to_sum }.
  End Eqv.

  Section EqvDec.
    Context {A} {E:EqvDec A}.

    Global Instance ext_top_bot_EqvDec : EqvDec (ext_top_bot A) :=
      { eqv_dec := eqv_dec `on` ext_top_bot_to_sum }.
  End EqvDec.

  Section Ord.
    Context {A} {E:Ord A}.

    Global Instance ext_top_bot_Ord : Ord (ext_top_bot A) :=
      { lt := lt `on` ext_top_bot_to_sum }.
  End Ord.

  Section OrdDec.
    Context {A} {O:OrdDec A}.

    Global Instance ext_top_bot_OrdDec : OrdDec (ext_top_bot A) :=
      { ord_dec := ord_dec `on` ext_top_bot_to_sum }.
  End OrdDec.

  Section Lattice.
    Context {A} {L:Lattice A} {O:Ord A} {LWF:LatticeWF A}.

    Definition ext_top_bot_meet (e1:ext_top_bot A) (e2:ext_top_bot A)
        : ext_top_bot A := ExtTopBot $
      match un_ext_top_bot e1, un_ext_top_bot e2 with
      | None, e2 => e2
      | e1, None => e1
      | Some None, _ => Some None
      | _, Some None => Some None
      | Some (Some a1), Some (Some a2) => Some $ Some (a1 /\ a2)
      end.

    Definition ext_top_bot_join (e1:ext_top_bot A) (e2:ext_top_bot A)
        : ext_top_bot A := ExtTopBot $
      match un_ext_top_bot e1, un_ext_top_bot e2 with
      | None, _ => None
      | _, None => None
      | Some None, e2 => e2
      | e1, Some None => e1
      | Some (Some a1), Some (Some a2) => Some $ Some (a1 \/ a2)
      end.

    Definition ext_top_bot_top : ext_top_bot A := ExtTopBot None.
    Definition ext_top_bot_bot : ext_top_bot A := ExtTopBot $ Some None.

    Global Instance ext_top_bot_Lattice : Lattice (ext_top_bot A) :=
      { lmeet := ext_top_bot_meet
      ; ljoin := ext_top_bot_join
      }.
    Global Instance ext_top_bot_BoundedLattice : BoundedLattice (ext_top_bot A) :=
      { ltop := ext_top_bot_top
      ; lbot := ext_top_bot_bot
      }.

    Definition foo {A} {OA:Ord A} (a:option (option A))
                                  (b:option (option A)) : Prop :=
              a <= b -> ExtTopBot a <= ExtTopBot b.
    Axiom bar :
      forall {A} {OA:Ord A} (a:option (option A)) (b:option (option A)), foo a b.

    Definition ext_top_bot_meet_ineq
        : forall e1 e2:ext_top_bot A, (e1 /\ e2) <= e1 `and` (e1 /\ e2) <= e2.
      intros ; simpl.
      destruct e1 as [e1], e2 as [e2] ; simpl in * ;
      destruct e1 as [e1|], e2 as [e2|] ; simpl in * ;
      [ destruct e1 as [e1|], e2 as [e2|]
      | destruct e1 as [e1|]
      | destruct e2 as [e2|]
      | idtac ] ; simpl in * ;
      unfold ext_top_bot_meet ; simpl in *;
        repeat
          match goal with
          | [ |- and _ _ ] => split
                                (*
          | [ |- or (sum_lt (inl (inr (?a /\ ?b))) (inl (inr ?a))) _ ] => left
*)
          | [ |- _ < _ ] => econstructor
          | [ |- sum_lt _ _ ] => econstructor
          | [ |- _ < _ ] => econstructor
          | [ |- (?a /\ ?b) < ?a ] => econstructor
          | _ => auto
          end.
      apply bar.
      destruct (lmeet_ineq e1 e2).
      apply lmeet_ineq.
      
      econstructor.
          
      unfold sum_lt.
      simpl.
      rewrite (inl_resp_eqv _ _.
      destruct (lmeet_ineq e1 e2) as [meet_l meet_r].
      destruct meet_l, meet_r.
      split.
        left ; econstructor ; econstructor ; auto.
        left ; econstructor ; econstructor ; auto.
      split.
        left ; econstructor ; econstructor ; auto.
        right ; econstructor ; econstructor ; auto.
      split.
        right ; econstructor ; econstructor ; auto.
        left ; econstructor ; econstructor ; auto.
      split.
        right ; econstructor ; econstructor ; auto.
        right ; econstructor ; econstructor ; auto.
      split.
        left ; econstructor ; econstructor.
        right ; econstructor ; econstructor ; reflexivity.
      split.
        right ; econstructor ; econstructor ; reflexivity.
        left ; econstructor ; econstructor.
      split.
        right ; econstructor ; econstructor ; reflexivity.
        right ; econstructor ; econstructor ; reflexivity.
      split.
        right ; econstructor ; econstructor ; reflexivity.
        left ; econstructor ; econstructor.
      split.
        right ; econstructor ; econstructor ; reflexivity.
        left ; econstructor ; econstructor.
      split.
        left ; econstructor ; econstructor.
        right ; econstructor ; econstructor ; reflexivity.
      split.
        left ; econstructor ; econstructor.
        right ; econstructor ; econstructor ; reflexivity.
      split.
        right ; econstructor ; econstructor ; reflexivity.
        right ; econstructor ; econstructor ; reflexivity.
      Qed.
  End Lattice.
End ext_top_bot.
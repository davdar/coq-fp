Require Export FP.Data.SumPre.

Require Import FP.Data.AsciiPre.
Require Import FP.Data.BoolPre.
Require Import FP.Data.StringPre.

Require Import FP.Data.Function.
Require Import FP.Relations.RelDec.
Require Import FP.Structures.EqDec.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Monad.
Require Import FP.Structures.MonadError.
Require Import FP.Structures.MonadFix.
Require Import FP.Structures.MonadPlus.
Require Import FP.Structures.Monoid.
Require Import FP.Structures.Ord.
Require Import FP.Structures.RelationClasses.
Require Import FP.Structures.Show.
Require Import FP.Structures.Injection.
Require Import FP.Data.Identity.
Require Import FP.Relations.Function.
Require Import FP.Relations.Setoid.

Import RespectNotation.
Import CharNotation.
Import EqDecNotation.
Import EqvNotation.
Import FunctionNotation.
Import MonadNotation.
Import MonoidNotation.
Import OrdNotation.
Import StringNotation.
Import LatticeNotation.

Local Infix "+" := sum.

Create HintDb sum_db.

Section Injection.
  Context {A B:Type}.
  Global Instance sum_Injection_inl : Injection A (A+B) inl := {}.
  Global Instance sum_Injection_inr : Injection B (A+B) inr := {}.
End Injection.

Section EqDec.
  Context {A B} {AED:EqDec A} {BED:EqDec B}.

  Definition sum_eq_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 =! a2
    | inr b1, inr b2 => b1 =! b2
    | _, _ => false
    end.

  Global Instance sum_EqDec : EqDec (A+B) := { eq_dec := sum_eq_dec }.

  Context {ARDC:RelDecCorrect (T:=A) eq_dec eq}.
  Context {BRDC:RelDecCorrect (T:=B) eq_dec eq}.

  Global Instance sum_Eq_RelDecCorrect : RelDecCorrect (T:=A+B) eq_dec eq.
    constructor ; intros.
    destruct x as [xl | xr], y as [yl | yr] ; constructor ; intros ;
      simpl in * ; repeat
        match goal with
        | [ H : _ =! _ = true |- _ ] => rewrite rel_dec_correct in H
        | [ |- _ =! _ = true ] => apply rel_dec_correct
        | _ => auto
        end ; try congruence.
    Qed.
End EqDec.

Section Eqv.
  Context {A B} {AE:Eqv A} {BE:Eqv B}.

  Inductive sum_eqv : A+B -> A+B -> Prop :=
    | InlSumEqv : forall a1 a2 , a1 ~= a2 -> sum_eqv (inl a1) (inl a2)
    | InrSumEqv : forall b1 b2, b1 ~= b2 -> sum_eqv (inr b1) (inr b2).

  Global Instance sum_Eqv : Eqv (A+B) := { eqv := sum_eqv }.

  Context {AEE:EqvWF A} {BEE:EqvWF B}.

  Global Instance sum_EqvWF : EqvWF (A+B).
    Local Ltac mysimp :=
      match goal with
      | [ |- inl _ ~= inl _ ] => constructor
      | [ |- inr _ ~= inr _ ] => constructor
      | [ |- ?x ~= ?x ] => reflexivity

      | [ H : inl _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ ~= inr _ |- _ ] => inversion H
      | [ H : inr _ ~= inl _ |- _ ] => inversion H
      | [ H : inr _ ~= inr _ |- _ ] => inversion H ; subst ; clear H

      | [ H : ?x ~= ?y |- ?y ~= ?x ] => symmetry ; exact H
      | [ H1 : ?x ~= ?y, H2 : ?y ~= ?z |- ?x ~= ?z ] =>
          transitivity y ; [exact H1 | exact H2]
      | _ => auto
      end.
    constructor ; constructor ; intros.
    unfold Reflexive ; intros.
      destruct x ; repeat mysimp.
    unfold Symmetric ; intros.
      destruct x as [xl | xr], y as [yl | yr] ; repeat mysimp.
    unfold Transitive ; intros.
      destruct x as [xl | xr], y as [yl | yr], z as [zl | zr] ; repeat mysimp.
    Qed.

  Global Instance sum_InjectionRespect_eqv_inl : InjectionRespect A (A+B) inl eqv eqv.
    constructor ; unfold Proper ; unfold "==>"%signature ; unfold "<==" ; intros ;
      simpl in *.
    constructor ; auto.
    inversion H ; auto.
    Qed.

  Global Instance sum_InjectionRespect_eqv_inr : InjectionRespect B (A+B) inr eqv eqv.
    constructor ; unfold Proper ; unfold "==>"%signature ; unfold "<==" ; intros ;
      simpl in *.
    constructor ; auto.
    inversion H ; auto.
    Qed.
End Eqv.

Section EqvDec.
  Context {A B} {AED:EqvDec A} {BED:EqvDec B}.

  Definition sum_eqv_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 ~=! a2
    | inr b1, inr b2 => b1 ~=! b2
    | _, _ => false
    end.

  Global Instance sum_EqvDec : EqvDec (A+B) := { eqv_dec := sum_eqv_dec }.

  Context {AE:Eqv A} {ARDC:RelDecCorrect (T:=A) eqv_dec eqv}.
  Context {BE:Eqv B} {BRDC:RelDecCorrect (T:=B) eqv_dec eqv}.

  Global Instance sum_Eqv_RelDecCorrect : RelDecCorrect (T:=A+B) eqv_dec eqv.
    constructor ; intros.
    destruct x as [xl | xr], y as [yl | yr] ; constructor ; intros ;
      simpl in * ; repeat 
        match goal with
        | [ |- _ ~=! _ = true ] => apply rel_dec_correct
        | [ |- sum_eqv _ _ ] => constructor
        | [ H : _ ~=! _ = true |- _ ] => rewrite rel_dec_correct in H
        | [ H : sum_eqv _ _ |- _ ] => inversion H ; clear H
        | _ => auto
        end ; try congruence.
    Qed.
End EqvDec.

Section Ord.
  Context {A B} {AL:Ord A} {BL:Ord B}.

  Inductive sum_lt : A+B -> A+B -> Prop :=
    | InlSumLte : forall a1 a2, a1 < a2 -> sum_lt (inl a1) (inl a2)
    | InrSumLte : forall b1 b2, b1 < b2 -> sum_lt (inr b1) (inr b2)
    | MisSumLte : forall a1 b2, sum_lt (inl a1) (inr b2).
      
  Global Instance sum_Ord : Ord (A+B) := { lt := sum_lt }.

  Context {ALWF:OrdWF A} {BLWF:OrdWF B}.

  Global Instance sum_OrdWF : OrdWF (A+B).
    Local Ltac mysimp :=
      match goal with
      | [ |- inl _ < inl _ ] => constructor
      | [ |- inl _ < inr _ ] => constructor
      | [ |- inr _ < inr _ ] => constructor
      | [ H : inl _ < inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ < inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ < inl _ |- _ ] => inversion H
      | [ H : inr _ < inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ ~= inr _ |- _ ] => inversion H
      | [ H : inr _ ~= inl _ |- _ ] => inversion H
      | [ H : inr _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : ?a < ?a |- False ] => apply (irreflexivity H)
      | [ H1 : ?a < ?b, H2 : ?b < ?c |- ?a < ?c ] =>
          transitivity b ; [exact H1 | exact H2]
      | [ H1 : ?a ~= ?a', H2 : ?b ~= ?b', H3 : ?a < ?b |- ?a' < ?b' ] =>
          eapply (lt_resp_eqv _ _ H1 _ _ H2) ; auto
      | [ H1 : ?a' ~= ?a, H2 : ?b' ~= ?b, H3 : ?a < ?b |- ?a' < ?b' ] =>
          eapply (lt_resp_eqv _ _ H1 _ _ H2) ; auto
      | _ => auto
      end.
    constructor.
    apply sum_EqvWF.
    unfold Irreflexive ; unfold Reflexive ; unfold complement ; intros.
      destruct x; repeat mysimp.
    unfold Transitive ; intros.
      destruct x, y, z ; repeat mysimp.
    unfold Proper ; unfold respectful ; intros t1 t2 e1 t3 t4 e2 ;
      constructor ; intros ;
      destruct t1, t2, t3, t4 ; repeat mysimp.
    Qed.

  Global Instance sum_InjectionRespect_lt_inl : InjectionRespect A (A+B) inl lt lt.
    constructor ; unfold Proper ; unfold "==>"%signature ; unfold "<==" ; intros.
    constructor ; auto.
    inversion H ; auto.
    Qed.
  Global Instance sum_InjectionRespect_lt_inr : InjectionRespect B (A+B) inr lt lt.
    constructor ; unfold Proper ; unfold "==>"%signature ; unfold "<==" ; intros.
    constructor ; auto.
    inversion H ; auto.
    Qed.
End Ord.

Section OrdDec.
  Context {A B:Type}.

  Definition sum_ord_dec_b
      (a_ord_dec:A -> A -> comparison) (b_ord_dec:B -> B -> comparison)
      (ab1:A+B) (ab2:A+B) : comparison :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 `a_ord_dec` a2
    | inr b1, inr b2 => b1 `b_ord_dec` b2
    | inl _, inr _ => Lt
    | inr _, inl _ => Gt
    end.

  Context {ALD:OrdDec A} {BLD:OrdDec B}.

  Definition sum_ord_dec : A+B -> A+B -> comparison := sum_ord_dec_b ord_dec ord_dec.

  Global Instance sum_OrdDec : OrdDec (A+B) := { ord_dec := sum_ord_dec }.

  Context {AO:Ord A} {BO:Ord B}.
  Context {ARDC:RelDecCorrect (T:=A) lt_dec lt}.
  Context {BRDC:RelDecCorrect (T:=B) lt_dec lt}.

  Lemma inl_lt_dec : forall a b, inl a <! inl b = true <-> a <! b = true.
    constructor ; intros ; unfold lt_dec in * ; simpl in * ; auto. Qed.
  Lemma inr_lt_dec : forall a b, inr a <! inr b = true <-> a <! b = true.
    constructor ; intros ; unfold lt_dec in * ; simpl in * ; auto. Qed.
  Lemma false_lt_dec : forall a b, inr a <! inl b = true -> False.
    intros ; unfold lt_dec in * ; simpl in * ; congruence. Qed.
  Global Instance sum_Ord_RelDecCorrect : RelDecCorrect (T:=A+B) lt_dec lt.
    constructor ; intros.
    destruct x, y ; constructor ; intros ; repeat
      match goal with
      | [ |- inl _ < inl _ ] => constructor
      | [ |- inr _ < inr _ ] => constructor
      | [ |- inl _ < inr _ ] => constructor
      | [ |- inl _ <! inl _ = true ] => apply inl_lt_dec
      | [ |- inr _ <! inr _ = true ] => apply inr_lt_dec
      | [ |- _ <! _ = true ] => apply rel_dec_correct
      | [ H : inl _ <! inl _ = true |- _ ] => apply inl_lt_dec in H
      | [ H : inr _ <! inr _ = true |- _ ] => apply inr_lt_dec in H
      | [ H : inr ?a <! inl ?b = true |- _ ] => exfalso ; apply (false_lt_dec a b H)
      | [ H : _ <! _ = true |- _ ] => apply rel_dec_correct in H
      | [ H : inl _ < inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ < inl _ |- _ ] => inversion H
      | [ H : inr _ < inr _ |- _ ] => inversion H ; subst ; clear H
      | _ => auto
      end.
    Qed.
End OrdDec.

Section Lattice.
  Context {A B:Type}.
  Context {AL:Lattice A} {BL:Lattice B}.

  Definition sum_meet (s1:A+B) (s2:A+B) : A+B :=
    match s1, s2 with
    | inl a1, inl a2 => inl $ a1 /\ a2
    | inl a1, inr _ => inl a1
    | inr _, inl a2 => inl a2
    | inr b1, inr b2 => inr $ b1 /\ b2
    end.
  Definition sum_join (s1:A+B) (s2:A+B) : A+B :=
    match s1,s2 with
    | inl a1, inl a2 => inl $ a1 \/ a2
    | inl _, inr b2 => inr b2
    | inr b1, inl _ => inr b1
    | inr b1, inr b2 => inr $ b1 \/ b2
    end.

  Global Instance sum_Lattice : Lattice (A+B) :=
    { lmeet := sum_meet
    ; ljoin := sum_join
    }.

  Context {AO:Ord A} {BO:Ord B}.
  Context {ALWF:LatticeWF A} {BLWF:LatticeWF B}.

  Lemma inlr_lte : forall (a:A) (b:B), inl a <= inr b.
    left ; constructor. Qed.

  Global Instance sum_LatticeWF : LatticeWF (A+B).
    Local Ltac mysimp :=
      match goal with
      | [ |- inl _ <= inl _ ] => eapply inject_resp_eta
      | [ |- inl _ <= inr _ ] => apply inlr_lte
      | [ |- inr _ <= inr _ ] => eapply inject_resp_eta
      | [ |- (?a /\ _) <= ?a ] => apply lmeet_ineq
      | [ |- (_ /\ ?a) <= ?a ] => apply lmeet_ineq
      | [ |- ?a <= (?a \/ _) ] => apply ljoin_ineq
      | [ |- ?a <= (_ \/ ?a) ] => apply ljoin_ineq
      | [ |- ?a <= ?a ] => reflexivity
      | _ => auto
      end.
    constructor ; intros.
    eauto with typeclass_instances.
    destruct t1, t2 ; constructor ; simpl ; repeat mysimp.
    destruct t1, t2 ; constructor ; simpl ; repeat mysimp.
    Qed.

  Context {ABL:BoundedLattice A} {BBL:BoundedLattice B}.

  Definition sum_top : A+B := inr ltop.
  Definition sum_bot : A+B := inl lbot.

  Global Instance sum_BoundedLattice : BoundedLattice (A+B) :=
    { ltop := sum_top
    ; lbot := sum_bot
    }.

  Context {ABLWF:BoundedLatticeWF A} {BBLWF:BoundedLatticeWF B}.

  Global Instance sum_BoundedLatticeWF : BoundedLatticeWF (A+B).
    constructor ; intros.
      destruct t.
        left ; constructor.
        destruct (ltop_ineq b).
          left ; constructor ; auto.
          right ; constructor ; auto.
      destruct t.
        destruct (lbot_ineq a).
          left ; constructor ; auto.
          right ; constructor ; auto.
        left ; constructor.
    Qed.
End Lattice.

Section Show.
  Context {A B} {AS:Show A} {BS:Show B}.

  Section sum_show.
    Variable (R:Type) (SR:ShowResult R).

    Definition sum_show (ab:A+B) : R :=
      let (tag, payload) :=
        match ab with
        | inl a => ("inl", show a)
        | inr b => ("inr", show b)
        end
      in raw_char "("%char
      ** raw_string tag
      ** raw_char " "%char
      ** payload
      ** raw_char ")"%char.
  End sum_show.

  Global Instance sum_Show : Show (A+B) := { show := sum_show }.
End Show.

Section Type_Monoid.
  Definition sum_Set_Monoid : Monoid Set :=
    {| monoid_times := (sum:Set -> Set -> Set)
     ; monoid_unit := Empty_set
    |}.
  Definition sum_Type_Monoid : Monoid Type :=
    {| monoid_times := sum
     ; monoid_unit := (Empty_set:Type)
    |}.
End Type_Monoid.

Inductive sum_t A m B := SumT { un_sum_t : m (A+B) }.
Arguments SumT {A m B} un_sum_t.
Arguments un_sum_t {A m B} _.

Section sum_t_Monad.
  Context {A:Type} {m} {M:Monad m}.

  Definition run_sum_t {B} : sum_t A m B -> m (A+B) := un_sum_t.

  Section Monad.
    Definition sum_t_ret {B} : B -> sum_t A m B := SumT '.' ret '.' inr.
    Definition sum_t_bind {B C}
        (bMM:sum_t A m B) (f:B -> sum_t A m C) : sum_t A m C :=
      SumT $ begin
        ab <- un_sum_t bMM ;;
        match ab with
        | inl x => ret $ inl x
        | inr y => un_sum_t $ f y
        end
      end.
    Global Instance sum_t_Monad : Monad (sum_t A m) :=
      { ret := @sum_t_ret
      ; bind := @sum_t_bind
      }.
  End Monad.

  Section MonadError.
    Definition sum_t_throw {B} : A -> sum_t A m B := SumT '.' ret '.' inl.
    Definition sum_t_catch {B}
        (bMM:sum_t A m B) (h:A -> sum_t A m B) : sum_t A m B :=
      SumT $ begin
        ab <-  un_sum_t bMM ;;
        match ab with
        | inl x => un_sum_t $ h x
        | inr y => ret $ inr y
        end
      end.
    Global Instance sum_t_MonadError : MonadError A (sum_t A m) :=
      { throw := @sum_t_throw
      ; catch := @sum_t_catch
      }.
  End MonadError.

  Section MonadPlus.
    Context {AM:Monoid A}.

    Definition sum_t_mzero {B} : sum_t A m B := SumT $ ret $ inl gunit.
    Definition sum_t_mplus {B C} (bMM:sum_t A m B) (cMM:sum_t A m C)
        : sum_t A m (B+C) :=
      SumT $ begin
        ab <- un_sum_t bMM ;;
        match ab with
        | inl e1 =>
            ac <- un_sum_t cMM ;;
            match ac with
            | inl e2 => ret $ inl $ e1 ** e2
            | inr c => ret $ inr $ inr c
            end
        | inr b => ret $ inr $ inl b
        end
      end.
    Global Instance sum_t_MonadPlus : MonadPlus (sum_t A m) :=
      { mzero := @sum_t_mzero
      ; mplus := @sum_t_mplus
      }.
  End MonadPlus.

  Section MonadFix.
    Context {MF:MonadFix m}.

    Definition sum_t_mfix {B C}
        (ff:(B -> sum_t A m C) -> B -> sum_t A m C) (b:B) : sum_t A m C :=
      let ff' (f':B -> m (A+C)) :=
        let f := SumT '.' f' in
        un_sum_t '.' ff f
      in
      SumT $ mfix ff' b.
    Global Instance sum_t_MonadFix : MonadFix (sum_t A m) :=
      { mfix := @sum_t_mfix }.
  End MonadFix.
End sum_t_Monad.

Instance sum_sum_t_FunctorInjection {A}
    : FunctorInjection (sum A) (sum_t A identity) :=
  { finject := fun _ => SumT '.' Identity }.
Instance sum_t_sum_FunctorInjection {A}
    : FunctorInjection (sum_t A identity) (sum A) :=
  { finject := fun _ => run_identity '.' run_sum_t }.
Instance sum_Monad {A} : Monad (sum A) := iso_Monad (sum_t A identity).
Instance sum_MonadPlus {A} {AM:Monoid A} : MonadPlus (sum A) :=
  iso_MonadPlus (sum_t A identity).
Instance sum_MonadError {A} : MonadError A (sum A) :=
  iso_MonadError (sum_t A identity).
  
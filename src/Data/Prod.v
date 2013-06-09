Require Import FP.CoreData.
Require Import FP.CoreClasses.
Require Import FP.Classes.
Require Import FP.Data.Type.

Import ClassesNotation.
Import CoreDataNotation.
Import CoreClassesNotation.

Section EqDec.
  Context {A B} `{! EqDec A ,! EqDec B }.

  Definition prod_eq_dec (ab1:A*B) (ab2:A*B) : bool :=
    let '((a1,b1),(a2,b2)) := (ab1,ab2) in
    a1 =! a2 && b1 =! b2.

  Global Instance prod_EqDec : EqDec (A*B) := { eq_dec := prod_eq_dec }.
End EqDec.
Global Instance prod_Bif_EqDec : Bif_EqDec prod := { bif_eq_dec := @prod_EqDec }.

Section Eq_RDC.
  Context {A B} `{! EqDec A ,! Eq_RDC A ,! EqDec B ,! Eq_RDC B }.

  Global Instance prod_Eq_RDC : Eq_RDC (A*B).
  Proof.
    repeat constructor ; intros ; destruct x,y ; simpl in * ; unfold prod_eq_dec in *
    ; repeat
        match goal with
        | [ H : (_,_) = (_,_) |- _ ] => inversion H ; subst ; clear H
        end ; simpl in * ; try congruence.
    - apply bool_conj_true ; constructor ; apply rel_correct ; reflexivity.
    - apply bool_conj_true in H ; destruct H.
      apply dec_correct in H ; rewrite H.
      apply dec_correct in H0 ; rewrite H0.
      reflexivity.
    Qed.
End Eq_RDC.
Global Instance prod_Bif_Eq_RDC : Bif_Eq_RDC prod := { bif_eq_rdc := @prod_Eq_RDC }.

Section Eqv.
  Context {A B} `{! Eqv A ,! Eqv B}.

  Inductive prod_eqv : A*B -> A*B -> Prop :=
    ProdEqv : forall a1 a2 b1 b2, a1 ~= a2 -> b1 ~= b2 -> prod_eqv (a1,b1) (a2,b2).

  Global Instance prod_Eqv : Eqv (A*B) := { eqv := prod_eqv }.
End Eqv.
Global Instance prod_Bif_Eqv : Bif_Eqv prod := { bif_eqv := @prod_Eqv }.

Section PER.
  Context {A B} `{! Eqv A ,! PER_WF A ,! Eqv B ,! PER_WF B}.
  Local Ltac mysimp :=
    match goal with
    | [ |- (_,_) ~= (_,_) ] => constructor
    | [ H : (_,_) ~= (_,_) |- _ ] => inversion H ; subst ; clear H
    end.
  Global Instance prod_PER_WF : PER_WF (A*B).
  Proof.
    constructor ; constructor ; intros.
    - unfold Symmetric ; intros.
      destruct x,y ; repeat mysimp ; symmetry ; auto.
    - unfold Transitive ; intros.
      destruct x,y,z ; repeat mysimp.
      + transitivity a0 ; auto.
      + transitivity b0 ; auto.
    Qed.
End PER.
Global Instance prod_Bif_PER_WF : Bif_PER_WF prod := { bif_per_wf := @prod_PER_WF }.

Section ER.
  Context {A B} `{! Eqv A ,! ER_WF A ,! Eqv B ,! ER_WF B}.
  Local Ltac mysimp :=
    match goal with
    | [ |- (_,_) ~= (_,_) ] => constructor
    | [ H : (_,_) ~= (_,_) |- _ ] => inversion H ; subst ; clear H
    end.
  Global Instance prod_ER_WF : ER_WF (A*B).
  Proof.
    constructor ; constructor ; intros.
    - unfold Reflexive ; intros.
      destruct x ; repeat mysimp ; reflexivity.
    - unfold Symmetric ; intros.
      destruct x,y ; repeat mysimp ; symmetry ; auto.
    - unfold Transitive ; intros.
      destruct x,y,z ; repeat mysimp.
      + transitivity a0 ; auto.
      + transitivity b0 ; auto.
    Qed.
End ER.
Global Instance prod_Bif_ER_WF : Bif_ER_WF prod := { bif_er_wf := @prod_ER_WF }.

Section EqvDec.
  Context {A B} `{! EqvDec A ,! EqvDec B }.

  Definition prod_eqv_dec (ab1:A*B) (ab2:A*B) : bool :=
    let '((a1,b1),(a2,b2)) := (ab1,ab2) in
    a1 ~=! a2 && b1 ~=! b2.

  Global Instance prod_EqvDec : EqvDec (A*B) := { eqv_dec := prod_eqv_dec }.
End EqvDec.
Global Instance prod_Bif_EqvDec : Bif_EqvDec prod := { bif_eqv_dec := @prod_EqvDec }.

Section Eqv_RDC.
  Context {A B} `{! Eqv A ,! EqvDec A ,! Eqv_RDC A ,! Eqv B ,! EqvDec B ,! Eqv_RDC B }.

  Global Instance prod_Eqv_RDC : Eqv_RDC (A*B).
  Proof.
    repeat constructor ; intros ; destruct x,y
    ; repeat 
        match goal with
        | [ |- and _ _ ] => constructor
        | [ |- (_,_) ~= (_,_) ] => constructor
        | [ |- (_,_) ~=! (_,_) = true ] => unfold "~=!" ; simpl ; unfold prod_eqv_dec
        | [ |- _ && _ = true ] => apply bool_conj_true
        | [ |- _ = true ] => apply rel_correct
        | [ H : (_,_) ~= (_,_) |- _ ] => inversion H ; subst ; clear H
        | [ H : (_,_) ~=! (_,_) = true |- _ ] => unfold "~=!" in H ; simpl in H ; unfold prod_eqv_dec in H
        | [ H : _ && _ = true |- _ ] => apply bool_conj_true in H ; destruct H
        | [ H : _ = true |- _ ] => apply dec_correct in H
        | _ => auto
        end.
    Qed.
End Eqv_RDC.
Global Instance prod_Bif_Eqv_RDC : Bif_Eqv_RDC prod := { bif_eqv_rdc := @prod_Eqv_RDC }.

Section Lte.
  Context {A B} `{! Lte A ,! Lte B }.

  Inductive prod_lte : A*B -> A*B -> Prop :=
    | FstProdLte : forall a1 a2 b1 b2, a1 < a2 -> prod_lte (a1,b1) (a2,b2)
    | SndProdLte : forall a1 a2 b1 b2, a1 <= a2 -> b1 <= b2 -> prod_lte (a1,b1) (a2,b2).
                      
  Global Instance prod_Lte : Lte (A*B) := { lte := prod_lte }.
End Lte.
Global Instance prod_Bif_Lte : Bif_Lte prod := { bif_lte := @prod_Lte }.

Section PreOrd.
  Context {A B} `{! Lte A ,! PreOrd A ,! Lte B ,! PreOrd B }.

  Global Instance prod_PreOrd : PreOrd (A*B).
  Proof.
    constructor.
    - unfold Reflexive ; intros.
      destruct x.
      apply SndProdLte ; reflexivity.
    - unfold Transitive ; intros.
      destruct x,y,z.
      inversion H ; subst ; clear H ; inversion H0 ; subst ; clear H0.
      + apply FstProdLte ; transitivity a0 ; auto.
      + apply FstProdLte.
        destruct H2 ; constructor ; [transitivity a0|] ; auto.
        unfold "~" ; intros ; apply H0.
        transitivity a1 ; auto.
      + apply FstProdLte.
        destruct H1 ; constructor ; [transitivity a0|] ; auto.
        unfold "~" ; intros ; apply H0.
        transitivity a ; auto.
      + apply SndProdLte ; [transitivity a0|transitivity b0] ; auto.
  Qed.
End PreOrd.
Global Instance prod_Bif_PreOrd : Bif_PreOrd prod := { bif_pre_ord := @prod_PreOrd }.

Section LteDec.
  Context {A B} `{! LteDec A ,! LteDec B }.

  Definition prod_lte_dec (ab1:A*B) (ab2:A*B) : bool :=
    let '((a1,b1),(a2,b2)) := (ab1,ab2) in
    match a1 <=! a2, a2 <=! a1 with
    | true, false => true
    | true, true => b1 <=! b2
    | _, _ => false
    end.
  Global Instance prod_LteDec : LteDec (A*B) := { lte_dec := prod_lte_dec }.
End LteDec.
Global Instance prod_Bif_LteDec : Bif_LteDec prod := { bif_lte_dec := @prod_LteDec }.

Section Lte_RDC.
  Context {A B} `{! Lte A ,! LteDec A ,! Lte_RDC A ,! Lte B ,! LteDec B ,! Lte_RDC B }.

  Global Instance prod_Lte_RDC : Lte_RDC (A*B).
  Proof.
    Local Ltac mysimp :=
      match goal with
      | [ |- (_,_) <=! (_,_) = true ] => unfold "<=!" ; simpl ; unfold prod_lte_dec
      | [ |- _ <=! _ = true ] => apply rel_correct
      | [ H : (_,_) <= (_,_) |- _ ] => inversion H ; subst ; clear H
      | [ H : (_,_) <=! (_,_) = true |- _ ] => unfold "<=!" in H ; simpl in H ; unfold prod_lte_dec in H
      | [ H : _ = _ <=! _ |- _ ] => symmetry in H
      | [ H : _ <=! _ = true |- _ ] => apply dec_correct in H
      | [ H : _ <=! _ = false |- _ ] => apply neg_dec_correct in H
      | _ => auto
      end.
    repeat constructor ; intros.
    - destruct x,y ; repeat mysimp.
      + destruct H1.
        apply rel_correct in H ; rewrite H.
        remember (a0 <=! a) as p ; destruct p ; auto.
        symmetry in Heqp ; apply dec_correct in Heqp.
        contradiction.
      + remember (a <=! a0) as p ; destruct p
        ; remember (a0 <=! a) as p ; destruct p ; repeat mysimp.
    - destruct x,y ; repeat mysimp.
      remember (a <=! a0) as p ; destruct p
      ; remember (a0 <=! a) as p ; destruct p ; repeat mysimp ; try congruence.
      * apply SndProdLte ; auto.
      * apply FstProdLte ; constructor ; auto.
  Qed.
End Lte_RDC.
Global Instance prod_Bif_Lte_RDC : Bif_Lte_RDC prod := { bif_lte_rdc := @prod_Lte_RDC }.

Section PartialOrd.
  Context {A B} `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B }.

  Global Instance prod_PartialOrd : PartialOrd (A*B).
  Proof.
    Local Ltac mysimp :=
      match goal with
      | [ |- (_,_) <=! (_,_) = true ] => unfold "<=!" ; simpl ; unfold prod_lte_dec
      | [ H : (_,_) ~= (_,_) |- _ ] => inversion H ; subst ; clear H
      | [ H : (_,_) <= (_,_) |- _ ] => inversion H ; subst ; clear H
      | [ H : (_,_) <=! (_,_) = true |- _ ] => unfold "<=!" in H ; simpl in H ; unfold prod_lte_dec in H
      | _ => auto
      end.
    constructor ; eauto with typeclass_instances.
    - unfold Antisymmetric ; intros.
      destruct x,y ; repeat mysimp.
      + destruct H1,H2 ; contradiction.
      + destruct H2 ; contradiction.
      + destruct H1 ; contradiction.
      + constructor ; apply antisymmetry ; auto.
    - unfold Proper,"==>",impl,Basics.impl ; intros.
      destruct x,y,x0,y0 ; repeat mysimp.
      + apply FstProdLte ; constructor.
        * rewrite <- H4 ; rewrite <- H5 ; destruct H0 ; auto.
        * unfold "~" ; intros ; destruct H0 as [H01 H02] ; apply H02.
          rewrite H4 ; rewrite H5 ; auto.
      + apply SndProdLte.
        * rewrite <- H4 ; rewrite <- H5 ; auto.
        * rewrite <- H7 ; rewrite <- H8 ; auto.
  Qed.
End PartialOrd.
Global Instance prod_Bif_PartialOrd : Bif_PartialOrd prod := { bif_partial_ord := @prod_PartialOrd }.

Section PartialOrdDec.
  Context {A B} `{! PartialOrdDec A ,! PartialOrdDec B }.

  Definition prod_pord_dec (ab1:A*B) (ab2:A*B) : option comparison :=
    let '((a1,b1),(a2,b2)) := (ab1,ab2) in
    match a1 <~>! a2 with
    | Some Lt => Some Lt
    | Some Eq => b1 <~>! b2
    | Some Gt => Some Gt
    | None => None
    end.

  Global Instance prod_PartialOrdDec : PartialOrdDec (A*B) := { pord_dec := prod_pord_dec }.
End PartialOrdDec.
Global Instance prod_Bif_PartialOrdDec : Bif_PartialOrdDec prod := { bif_partial_ord_dec := @prod_PartialOrdDec }.

Section PartialOrd_RDC.
  Context {A B}
    `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! PartialOrdDec A ,! PartialOrd_RDC A
     ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B ,! PartialOrdDec B ,! PartialOrd_RDC B
     }.

  Lemma lt_prod_destruct :
    forall (a1 a2:A) (b1 b2:B),
    (a1,b1) < (a2,b2) -> (a1 < a2 \/ (a1 ~= a2 /\ b1 < b2)).
  Proof.
    intros.
    destruct H.
    inversion H ; subst ; clear H ; auto.
    remember (a1 <~>! a2) as p ; destruct p ; [destruct c|] ; symmetry in Heqp
    ; repeat
        match goal with
        | [ H : _ <~>! _ = Some Eq |- _ ] => apply pord_dec_correct_eqv in H
        | [ H : _ <~>! _ = Some Lt |- _ ] => apply pord_dec_correct_lt in H
        | [ H : _ <~>! _ = Some Gt |- _ ] => apply pord_dec_correct_gt in H
        | [ H : _ <~>! _ = None |- _ ] => apply pord_dec_correct_un in H
        end.
    - right ; constructor ; auto.
      constructor ; auto.
      unfold "~" ; intros ; apply H0.
      apply SndProdLte ; auto.
      rewrite Heqp ; reflexivity.
    - left ; auto.
    - destruct Heqp ; contradiction.
    - destruct Heqp ; contradiction.
  Qed.

  Lemma un_prod_destruct :
    forall (a1 a2:A) (b1 b2:B),
    (a1,b1) >< (a2,b2) -> (a1 >< a2) \/ (a1 ~= a2 /\ b1 >< b2).
  Proof.
    intros.
    remember (a1 <~>! a2) as p ; destruct p ; symmetry in Heqp.
    - right.
      destruct H.
      destruct c.
      + apply pord_dec_correct_eqv in Heqp.
        constructor ; auto.
        constructor ; unfold "~" ; intros.
        * apply H.
          apply SndProdLte ; auto ; rewrite Heqp ; reflexivity.
        * apply H0.
          apply SndProdLte ; auto ; rewrite Heqp ; reflexivity.
      + exfalso ; apply H.
        apply pord_dec_correct_lt in Heqp.
        apply FstProdLte ; auto.
      + exfalso ; apply H0.
        apply pord_dec_correct_gt in Heqp.
        apply FstProdLte ; auto.
    - left.
      apply pord_dec_correct_un in Heqp ; auto.
  Qed.
            
  Global Instance prod_PartialOrd_RDC : PartialOrd_RDC (A*B).
  Proof.
    constructor ; intros ; destruct x,y ; simpl in * ; unfold prod_pord_dec
    ; repeat
        match goal with
        | [ |- (_,_) ~= (_,_) ] => constructor
        | [ H : and _ _ |- _ ] => destruct H
        | [ H : (_,_) ~= (_,_) |- _ ] => inversion H ; subst ; clear H
        | [ H : (_,_) <= (_,_) |- _ ] => inversion H ; subst ; clear H
        | [ H : (_,_) < (_,_) |- _ ] => apply lt_prod_destruct in H ; destruct H
        | [ H : (_,_) >< (_,_) |- _ ] => apply un_prod_destruct in H ; destruct H
        | [ H : _ ~= _ |- _ ] => apply pord_rel_correct_eqv in H ; rewrite H
        | [ H : _ ~= _ |- _ ] => symmetry in H ; apply pord_rel_correct_eqv in H ; rewrite H
        | [ H : _ < _ |- _ ] => apply pord_rel_correct_lt in H ; rewrite H
        | [ H : _ < _ |- _ ] => apply pord_rel_correct_gt in H ; rewrite H
        | [ H : _ >< _ |- _ ] => apply pord_rel_correct_un in H ; rewrite H
        | _ => auto
        end
    ; unfold prod_pord_dec in H ; remember (a <~>! a0) as p ; destruct p ; try destruct c
    ; try congruence ; symmetry in Heqp
    ; repeat
        match goal with
        | [ |- _ < _ ] => constructor
        | [ |- _ >< _ ] => constructor
        | [ |- ~ _ ] => unfold "~" ; intros
        | [ H : (_,_) <= (_,_) |- _ ] => inversion H ; subst ; clear H
        | [ H : _ <~>! _ = Some Eq |- _ ] => apply pord_dec_correct_eqv in H
        | [ H : _ <~>! _ = Some Lt |- _ ] => apply pord_dec_correct_lt in H
        | [ H : _ <~>! _ = Some Gt |- _ ] => apply pord_dec_correct_gt in H
        | [ H : _ <~>! _ = None |- _ ] => apply pord_dec_correct_un in H
        | [ H : _ < _ |- _ ] => destruct H
        | [ H : _ >< _ |- _ ] => destruct H
        | [ H : ?x ~= ?y |- (?x,_) <= (?y,_) ] => apply SndProdLte
        | [ H : ?y ~= ?x |- (?x,_) <= (?y,_) ] => apply SndProdLte
        | [ H1 : ?x <= ?y , H2 : ~ (?y <= ?x) |- (?x,_) <= (?y,_) ] => apply FstProdLte
        | [ H : ?x ~= ?y |- ?x <= ?y ] => rewrite H ; reflexivity
        | [ H : ?x ~= ?y |- ?y <= ?x ] => rewrite H ; reflexivity
        | [ H1 : ?x ~= ?y , H2 : ~ (?x <= ?y) |- False ] => apply H2
        | [ H1 : ?y ~= ?x , H2 : ~ (?x <= ?y) |- False ] => apply H2
        | _ => auto
        end.
  Qed.
End PartialOrd_RDC.
Global Instance prod_Bif_PartialOrd_RDC : Bif_PartialOrd_RDC prod := { bif_partial_ord_rdc := @prod_PartialOrd_RDC }.

Section TotalOrd.
  Context {A B} `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! Lte B ,! Eqv B ,! ER_WF B ,! TotalOrd B }.

  Global Instance prod_TotalOrd : TotalOrd (A*B).
  Proof.
    Local Ltac mysimp :=
      match goal with
      | _ => auto
      end.
    constructor ; eauto with typeclass_instances.
    intros ; unfold "~" at 1 ; intros H ; destruct H.
    destruct x,y.
    apply (TotalOrd_comparable a a0) ; constructor ; unfold "~" ; intros
    ; apply (TotalOrd_comparable b b0) ; constructor ; unfold "~" ; intros.
    - apply H ; apply SndProdLte ; auto.
    - assert (~~(a0 <= a)).
      { unfold "~" at 1 ; intros.
        apply H ; apply FstProdLte ; constructor ; auto.
      } 
      apply H3 ; unfold "~" ; intros.
      apply H0 ; apply SndProdLte ; auto.
    - assert (~~(a <= a0)).
      { unfold "~" at 1 ; intros.
        apply H0 ; apply FstProdLte ; constructor ; auto.
      }
      apply H3 ; unfold "~" ; intros.
      apply H ; apply SndProdLte ; auto.
    - apply H0 ; apply SndProdLte ; auto.
  Qed.
End TotalOrd.
Global Instance prod_Bif_TotalOrd : Bif_TotalOrd prod := { bif_total_ord := @prod_TotalOrd }.

Section TotalOrdDec.
  Context {A B} `{! TotalOrdDec A ,! TotalOrdDec B }.

  Definition prod_tord_dec (ab1:A*B) (ab2:A*B) : comparison :=
    let '((a1,b1),(a2,b2)) := (ab1,ab2) in
    match a1 <=>! a2 with
    | Lt => Lt
    | Eq => b1 <=>! b2
    | Gt => Gt
    end.

  Global Instance prod_TotalOrdDec : TotalOrdDec (A*B) := { tord_dec := prod_tord_dec }.
End TotalOrdDec.
Global Instance prod_Bif_TotalOrdDec : Bif_TotalOrdDec prod := { bif_total_ord_dec := @prod_TotalOrdDec }.

Section TotalOrd_RDC.
  Context {A B}
    `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! TotalOrdDec A ,! TotalOrd_RDC A
     ,! Lte B ,! Eqv B ,! ER_WF B ,! TotalOrd B ,! TotalOrdDec B ,! TotalOrd_RDC B
     }.

  Global Instance prod_TotalOrd_RDC : TotalOrd_RDC (A*B).
  Proof.
    constructor ; intros ; destruct x,y ; simpl in * ; unfold prod_tord_dec
    ; repeat
        match goal with
        | [ |- (_,_) ~= (_,_) ] => constructor
        | [ H : and _ _ |- _ ] => destruct H
        | [ H : (_,_) ~= (_,_) |- _ ] => inversion H ; subst ; clear H
        | [ H : (_,_) < (_,_) |- _ ] => apply lt_prod_destruct in H ; destruct H
        | [ H : _ ~= _ |- _ ] => apply tord_rel_correct_eqv in H ; rewrite H
        | [ H : _ ~= _ |- _ ] => symmetry in H ; apply tord_rel_correct_eqv in H ; rewrite H
        | [ H : _ < _ |- _ ] => apply tord_rel_correct_lt in H ; rewrite H
        | [ H : _ < _ |- _ ] => apply tord_rel_correct_gt in H ; rewrite H
        | _ => auto
        end
    ; unfold prod_tord_dec in H ; remember (a <=>! a0) as p ; destruct p ; try destruct c
    ; try congruence ; symmetry in Heqp
    ; repeat
        match goal with
        | [ |- _ <=>! _ = Lt ] => apply tord_rel_correct_lt
        | [ |- _ <=>! _ = Gt ] => apply tord_rel_correct_gt
        | [ |- _ < _ ] => constructor
        | [ |- ~ _ ] => unfold "~" ; intros
        | [ H : (_,_) <= (_,_) |- _ ] => inversion H ; subst ; clear H
        | [ H : _ <=>! _ = Eq |- _ ] => apply tord_dec_correct_eqv in H
        | [ H : _ <=>! _ = Lt |- _ ] => apply tord_dec_correct_lt in H
        | [ H : _ <=>! _ = Gt |- _ ] => apply tord_dec_correct_gt in H
        | [ H : _ < _ |- _ ] => destruct H
        | [ H : ?x ~= ?y |- (?x,_) <= (?y,_) ] => apply SndProdLte
        | [ H : ?y ~= ?x |- (?x,_) <= (?y,_) ] => apply SndProdLte
        | [ H1 : ?x <= ?y , H2 : ~ (?y <= ?x) |- (?x,_) <= (?y,_) ] => apply FstProdLte
        | [ H : ?x ~= ?y |- ?x <= ?y ] => rewrite H ; reflexivity
        | [ H : ?x ~= ?y |- ?y <= ?x ] => rewrite H ; reflexivity
        | [ H1 : ?x ~= ?y , H2 : ~ (?x <= ?y) |- _ ] => exfalso ; apply H2
        | [ H1 : ?y ~= ?x , H2 : ~ (?x <= ?y) |- _ ] => exfalso ; apply H2
        | _ => auto
        end ; try contradiction.
    - apply H1 ; apply SndProdLte ; [rewrite Heqp ; reflexivity|] ; auto.
    - apply H1 ; apply SndProdLte ; [rewrite Heqp ; reflexivity|] ; auto.
  Qed.
End TotalOrd_RDC.
Global Instance prod_Bif_TotalOrd_RDC : Bif_TotalOrd_RDC prod := { bif_total_ord_rdc := @prod_TotalOrd_RDC }.

Section Lattice.
  Context {A B} `{! Lattice A ,! Lattice B }.

  Definition prod_meet (s1:A*B) (s2:A*B) : A*B :=
    let '((a1,b1),(a2,b2)) := (s1,s2) in
    (a1 /\ a2, b1 /\ b2).
  Definition prod_join (s1:A*B) (s2:A*B) : A*B :=
    let '((a1,b1),(a2,b2)) := (s1,s2) in
    (a1 \/ a2, b1 \/ b2).

  Global Instance prod_Lattice : Lattice (A*B) :=
    { lmeet := prod_meet
    ; ljoin := prod_join
    }.
End Lattice.
Global Instance prod_Bif_Lattice : Bif_Lattice prod := { bif_lattice := @prod_Lattice }.

Section LatticeWF.
  Context {A B}
    `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! Lattice A ,! LatticeWF A
     ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B ,! Lattice B ,! LatticeWF B
     }.

  Global Instance prod_LatticeWF : LatticeWF (A*B).
  Proof.
    constructor ; intros ; destruct t1,t2 ; unfold "/\","\/" ; simpl
    ; unfold prod_meet,prod_join ; constructor
    ; destruct (lmeet_ineq a a0) ; destruct (lmeet_ineq b b0)
    ; destruct (ljoin_ineq a a0) ; destruct (ljoin_ineq b b0)
    ; apply SndProdLte ; auto.
  Qed.
End LatticeWF.
Global Instance prod_Bif_LatticeWF : Bif_LatticeWF prod := { bif_lattice_wf := @prod_LatticeWF }.

Section BoundedLattice.
  Context {A B} `{! BoundedLattice A ,! BoundedLattice B }.

  Definition prod_top : A*B := (ltop,ltop).
  Definition prod_bot : A*B := (lbot,lbot).

  Global Instance prod_BoundedLattice : BoundedLattice (A*B) :=
    { ltop := prod_top
    ; lbot := prod_bot
    }.
End BoundedLattice.
Global Instance prod_Bif_BoundedLattice : Bif_BoundedLattice prod := { bif_bounded_lattice := @prod_BoundedLattice }.

Section BoundedLatticeWF.
  Global Instance prod_BoundedLatticeWF {A B}
    `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! Lattice A ,! BoundedLattice A ,! LatticeWF A ,! BoundedLatticeWF A
     ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B ,! Lattice B ,! BoundedLattice B ,! LatticeWF B ,! BoundedLatticeWF B
     } : BoundedLatticeWF (A*B).
  Proof.
    constructor ; eauto with typeclass_instances ; intros ; destruct t
    ; apply SndProdLte ; try apply ltop_ineq ; apply lbot_ineq.
  Qed.
End BoundedLatticeWF.
Global Instance prod_Bif_BoundedLatticeWF : Bif_BoundedLatticeWF prod := { bif_bounded_lattice_wf := @prod_BoundedLatticeWF }.

Definition sequence_fst {t A B} `{! Applicative t } (p:t A*B)  : t (A*B) :=
  let (aT,b) := p in fret pair <@> aT <@> fret b.

Definition sequence_snd {t A B} `{! Applicative t } (p:A*t B)  : t (A*B) :=
  let (a,bT) := p in fret pair <@> fret a <@> bT.

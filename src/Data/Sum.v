Require Import FP.CoreData.
Require Import FP.CoreClasses.
Require Import FP.Categories.

Import CoreClassesNotation.
Import CoreDataNotation.

Section Injection.
  Context {A B} `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B }.

  Global Instance sum_IR_inl_eq : InjectionRespect A (A+B) inl eq eq.
  Proof. constructor ; unfold Proper ; simpl in * ; intros ; congruence. Qed.
  Global Instance sum_IR_inr_eq : InjectionRespect B (A+B) inr eq eq.
  Proof. constructor ; unfold Proper ; simpl in * ; intros ; congruence. Qed.
End Injection.

Section EqDec.
  Context {A B} `{! EqDec A ,! EqDec B }.

  Definition sum_eq_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 =! a2
    | inr b1, inr b2 => b1 =! b2
    | _, _ => false
    end.

  Global Instance sum_EqDec : EqDec (A+B) := { eq_dec := sum_eq_dec }.
End EqDec.
Global Instance sum_Bif_EqDec : Bif_EqDec sum := { bif_eq_dec := @sum_EqDec }.

Section Eq_RDC.
  Context {A B} `{! EqDec A ,! Eq_RDC A ,! EqDec B ,! Eq_RDC B }.

  Global Instance sum_Eq_RDC : Eq_RDC (A+B).
  Proof. repeat constructor ; intros ;
    destruct x as [xl | xr], y as [yl | yr] ; intros ;
      simpl in * ; repeat
        match goal with
        | [ H : _ =! _ = true |- _ ] => apply dec_correct in H
        | [ |- _ =! _ = true ] => apply rel_correct
        | _ => auto
        end ; try congruence.
    Qed.
End Eq_RDC.
Global Instance sum_Bif_Eq_RDC : Bif_Eq_RDC sum := { bif_eq_rdc := @sum_Eq_RDC }.

Section Eqv.
  Context {A B} `{! Eqv A ,! Eqv B}.

  Inductive sum_eqv : A+B -> A+B -> Prop :=
    | InlSumEqv : forall a1 a2 , a1 ~= a2 -> sum_eqv (inl a1) (inl a2)
    | InrSumEqv : forall b1 b2, b1 ~= b2 -> sum_eqv (inr b1) (inr b2).

  Global Instance sum_Eqv : Eqv (A+B) := { eqv := sum_eqv }.

  Global Instance sum_IR_inl_eqv : InjectionRespect A (A+B) inl eqv eqv.
  Proof.
    constructor ; unfold Proper ; simpl in * ; intros.
    constructor ; auto.
    unfold "<==" ; intros ; inversion H ; auto.
  Qed.

  Global Instance sum_IR_inr_eqv : InjectionRespect B (A+B) inr eqv eqv.
  Proof.
    constructor ; unfold Proper ; simpl in * ; intros.
    constructor ; auto.
    unfold "<==" ; intros ; inversion H ; auto.
  Qed.
End Eqv.
Global Instance sum_Bif_Eqv : Bif_Eqv sum := { bif_eqv := @sum_Eqv }.

Section PER.
  Context {A B} `{! Eqv A ,! PER_WF A ,! Eqv B ,! PER_WF B}.
  Global Instance sum_PER_WF : PER_WF (A+B).
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
    unfold Symmetric ; intros.
      destruct x as [xl | xr], y as [yl | yr] ; repeat mysimp.
    unfold Transitive ; intros.
      destruct x as [xl | xr], y as [yl | yr], z as [zl | zr] ; repeat mysimp.
    Qed.
End PER.
Global Instance sum_Bif_PER_WF : Bif_PER_WF sum := { bif_per_wf := @sum_PER_WF }.

Section ER.
  Context {A B} `{! Eqv A ,! ER_WF A ,! Eqv B ,! ER_WF B}.
  Global Instance sum_ER_WF : ER_WF (A+B).
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
End ER.
Global Instance sum_Bif_ER_WF : Bif_ER_WF sum := { bif_er_wf := @sum_ER_WF }.

Section EqvDec.
  Context {A B} `{! EqvDec A ,! EqvDec B }.

  Definition sum_eqv_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1, ab2 with
    | inl a1, inl a2 => a1 ~=! a2
    | inr b1, inr b2 => b1 ~=! b2
    | _, _ => false
    end.

  Global Instance sum_EqvDec : EqvDec (A+B) := { eqv_dec := sum_eqv_dec }.
End EqvDec.
Global Instance sum_Bif_EqvDec : Bif_EqvDec sum := { bif_eqv_dec := @sum_EqvDec }.

Section Eqv_RDC.
  Context {A B} `{! Eqv A ,! EqvDec A ,! Eqv_RDC A ,! Eqv B ,! EqvDec B ,! Eqv_RDC B }.

  Global Instance sum_Eqv_RDC : Eqv_RDC (A+B).
  Proof. repeat constructor ; intros ;
    destruct x as [xl | xr], y as [yl | yr] ; intros ;
      simpl in * ; repeat 
        match goal with
        | [ H : inl _ ~=! _ = _ |- _ ] => unfold "~=!" in H ; simpl in H
        | [ H : inr _ ~=! _ = _ |- _ ] => unfold "~=!" in H ; simpl in H
        | [ |- inl _ ~=! _ = _ ] => unfold "~=!" ; simpl
        | [ |- inr _ ~=! _ = _ ] => unfold "~=!" ; simpl
        | [ |- _ ~=! _ = true ] => apply rel_correct
        | [ |- _ ~= _ ] => constructor
        | [ H : _ ~=! _ = true |- _ ] => apply dec_correct in H
        | [ H : _ ~= _ |- _ ] => inversion H ; clear H
        | _ => auto
        end ; try congruence.
    Qed.
End Eqv_RDC.
Global Instance sum_Bif_Eqv_RDC : Bif_Eqv_RDC sum := { bif_eqv_rdc := @sum_Eqv_RDC }.

Section Lte.
  Context {A B} `{! Lte A ,! Lte B }.

  Inductive sum_lte : A+B -> A+B -> Prop :=
    | InlSumLte : forall a1 a2, a1 <= a2 -> sum_lte (inl a1) (inl a2)
    | InrSumLte : forall b1 b2, b1 <= b2 -> sum_lte (inr b1) (inr b2)
    | LRSumLte : forall a1 b2, sum_lte (inl a1) (inr b2).
                      
  Global Instance sum_Lte : Lte (A+B) := { lte := sum_lte }.

  Global Instance sum_IR_inl_lte : InjectionRespect A (A+B) inl lte lte.
  Proof.
    constructor ; unfold Proper,"==>","<==" ; intros.
    - constructor ; auto. 
    - inversion H ; auto.
  Qed.

  Global Instance sum_IR_inr_lte : InjectionRespect B (A+B) inr lte lte.
  Proof.
    constructor ; unfold Proper,"==>","<==" ; intros.
    - constructor ; auto. 
    - inversion H ; auto.
  Qed.
End Lte.
Global Instance sum_Bif_Lte : Bif_Lte sum := { bif_lte := @sum_Lte }.

Section PreOrd.
  Context {A B} `{! Lte A ,! PreOrd A ,! Lte B ,! PreOrd B }.

  Global Instance sum_PreOrd : PreOrd (A+B).
  Proof.
    Local Ltac mysimp :=
      match goal with
      | [ |- inl _ <= inl _ ] => constructor
      | [ |- inl _ <= inr _ ] => constructor
      | [ |- inr _ <= inr _ ] => constructor
      | [ H : inl _ <= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ <= inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ <= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ <= inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H1 : ?x <= ?y , H2 : ?y <= ?z |- ?x <= ?z ] => transitivity y ; auto
      | _ => auto
      end.
    constructor.
    - unfold Reflexive ; intros.
      destruct x ; repeat mysimp ; reflexivity.
    - unfold Transitive ; intros.
      destruct x,y,z ; repeat mysimp.
  Qed.
End PreOrd.
Global Instance sum_Bif_PreOrd : Bif_PreOrd sum := { bif_pre_ord := @sum_PreOrd }.

Section LteDec.
  Context {A B} `{! LteDec A ,! LteDec B }.

  Definition sum_lte_dec (ab1:A+B) (ab2:A+B) : bool :=
    match ab1,ab2 with
    | inl a1,inl a2 => a1 <=! a2
    | inl _,inr _ => true
    | inr _,inl _ => false
    | inr b1,inr b2 => b1 <=! b2
    end.
  Global Instance sum_LteDec : LteDec (A+B) := { lte_dec := sum_lte_dec }.
End LteDec.
Global Instance sum_Bif_LteDec : Bif_LteDec sum := { bif_lte_dec := @sum_LteDec }.

Section Lte_RDC.
  Context {A B} `{! Lte A ,! LteDec A ,! Lte_RDC A ,! Lte B ,! LteDec B ,! Lte_RDC B }.

  Global Instance sum_Lte_RDC : Lte_RDC (A+B).
  Proof.
    Local Ltac mysimp :=
      match goal with
      | [ |- inl _ <= inl _ ] => constructor
      | [ |- inl _ <= inr _ ] => constructor
      | [ |- inr _ <= inr _ ] => constructor
      | [ |- _ <= _ ] => apply dec_correct
      | [ H : inl _ <= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ <= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ <= inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : _ <= _ |- _ ] => apply rel_correct in H
      | [ H : inr _ <=! inl _ = true |- _ ] => discriminate H
      | _ => auto
      end.
    repeat constructor ; intros.
    - destruct x,y ; repeat mysimp.
    - destruct x,y ; repeat mysimp.
  Qed.
End Lte_RDC.
Global Instance sum_Bif_Lte_RDC : Bif_Lte_RDC sum := { bif_lte_rdc := @sum_Lte_RDC }.

Section PartialOrd.
  Context {A B} `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B }.

  Global Instance sum_PartialOrd : PartialOrd (A+B).
  Proof.
    Local Ltac mysimp :=
      match goal with
      | [ |- inl _ ~= inl _ ] => constructor
      | [ |- inr _ ~= inr _ ] => constructor
      | [ |- inl _ <= inl _ ] => constructor
      | [ |- inl _ <= inr _ ] => constructor
      | [ |- inr _ <= inr _ ] => constructor
      | [ H : inl _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ <= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ <= inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ <= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ <= inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H1 : ?x <= ?y , H2 : ?y <= ?x |- ?x ~= ?y ] => apply antisymmetry ; auto
      | [ H1 : ?x <= _ , H2 : ?x0 ~= ?x |- ?x0 <= _ ] => rewrite H2
      | [ H1 : _ <= ?y , H2 : ?y0 ~= ?y |- _ <= ?y0 ] => rewrite H2
      | _ => auto
      end.
    constructor ; eauto with typeclass_instances.
    - unfold Antisymmetric ; intros.
      destruct x,y ; repeat mysimp.
    - unfold Proper,"==>",impl,Basics.impl ; intros.
      destruct x,y,x0,y0 ; repeat mysimp.
      rewrite <- H3 ; rewrite <- H4 ; auto.
      rewrite <- H3 ; rewrite <- H4 ; auto.
  Qed.
End PartialOrd.
Global Instance sum_Bif_PartialOrd : Bif_PartialOrd sum := { bif_partial_ord := @sum_PartialOrd }.

Section PartialOrdDec.
  Context {A B} `{! PartialOrdDec A ,! PartialOrdDec B }.

  Definition sum_pord_dec (ab1:A+B) (ab2:A+B) : option comparison :=
    match ab1,ab2 with
    | inl a1,inl a2 => a1 <~>! a2
    | inl _,inr _ => Some Lt
    | inr _,inl _ => Some Gt
    | inr b1,inr b2 => b1 <~>! b2
    end.

  Global Instance sum_PartialOrdDec : PartialOrdDec (A+B) := { pord_dec := sum_pord_dec }.
End PartialOrdDec.
Global Instance sum_Bif_PartialOrdDec : Bif_PartialOrdDec sum := { bif_partial_ord_dec := @sum_PartialOrdDec }.

Section PartialOrd_RDC.
  Context {A B}
    `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! PartialOrdDec A ,! PartialOrd_RDC A
     ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B ,! PartialOrdDec B ,! PartialOrd_RDC B
     }.

  Global Instance sum_PartialOrd_RDC : PartialOrd_RDC (A+B).
  Proof.
    Local Ltac mysimp :=
      match goal with
      | [ |- inl _ ~= inl _ ] => constructor
      | [ |- inr _ ~= inr _ ] => constructor
      | [ |- inl _ <= inr _ ] => constructor
      | [ |- inr _ <= inr _ ] => constructor
      | [ |- inl _ < inl _ ] => apply InjectionRespect_eta
      | [ |- inl _ < inr _ ] => constructor
      | [ |- inr _ < inr _ ] => apply InjectionRespect_eta
      | [ |- inl _ >< inl _ ] => apply InjectionRespect_eta
      | [ |- inr _ >< inr _ ] => apply InjectionRespect_eta
      | [ |- _ <~>! _ = Some Eq ] => apply pord_rel_correct_eqv
      | [ |- _ <~>! _ = Some Lt ] => apply pord_rel_correct_lt
      | [ |- _ <~>! _ = Some Gt ] => apply pord_rel_correct_gt
      | [ |- _ <~>! _ = None ] => apply pord_rel_correct_un
      | [ H : inl _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ <= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : ~ inl _ <= inr _ |- _ ] => exfalso ; apply H
      | [ H : inr _ <= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ < inl _ |- _ ] => apply InjectionRespect_beta in H
      | [ H : inr _ < inr _ |- _ ] => apply InjectionRespect_beta in H
      | [ H : inr _ < inl _ |- _ ] => destruct H
      | [ H : inl _ >< inl _ |- _ ] => apply InjectionRespect_beta in H
      | [ H : inl _ >< inr _ |- _ ] => destruct H
      | [ H : inr _ >< inl _ |- _ ] => destruct H
      | [ H : inr _ >< inr _ |- _ ] => destruct H
      | [ H : inl _ <~>! inr _ = Some Eq |- _ ] => discriminate H
      | [ H : _ <~>! _ = Some Eq |- _ ] => apply pord_dec_correct_eqv in H
      | [ H : _ <~>! _ = Some Lt |- _ ] => apply pord_dec_correct_lt in H
      | [ H : _ <~>! _ = Some Gt |- _ ] => apply pord_dec_correct_gt in H
      | [ H : _ <~>! _ = None |- _ ] => apply pord_dec_correct_un in H
      | [ H1 : ~ inr ?x <= inr ?y , H2 : ~ inr ?y <= inr ?x |- ?x >< ?y ] =>
          constructor ; unfold "~" ; intros ; [ apply H1 | apply H2]
      | [ |- ~ inr _ <= inl _ ] => unfold "~" ; intros
      | _ => auto
      end.
    constructor ; intros ; destruct x,y ; simpl in * ; repeat mysimp ; try congruence.
  Qed.
End PartialOrd_RDC.
Global Instance sum_Bif_PartialOrd_RDC : Bif_PartialOrd_RDC sum := { bif_partial_ord_rdc := @sum_PartialOrd_RDC }.

Section TotalOrd.
  Context {A B} `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! Lte B ,! Eqv B ,! ER_WF B ,! TotalOrd B }.

  Global Instance sum_TotalOrd : TotalOrd (A+B).
    Proof.
      Local Ltac mysimp :=
        match goal with
        | [ |- inl _ <= inl _ ] => constructor
        | [ |- inl _ <= inr _ ] => constructor
        | [ |- inr _ <= inr _ ] => constructor
        | _ => auto
        end.
      constructor ; eauto with typeclass_instances ; intros.
      unfold "~" at 1 ; intros H ; destruct H.
      destruct x,y.
      - apply (TotalOrd_comparable (x:=a) (y:=a0))
        ; constructor ; unfold "~" ; intros ; [ apply H | apply H0 ]
        ; repeat mysimp.
      - apply H ; repeat mysimp.
      - apply H0 ; repeat mysimp.
      - apply (TotalOrd_comparable (x:=b) (y:=b0))
        ; constructor ; unfold "~" ; intros ; [ apply H | apply H0 ]
        ; repeat mysimp.
    Qed.
End TotalOrd.
Global Instance sum_Bif_TotalOrd : Bif_TotalOrd sum := { bif_total_ord := @sum_TotalOrd }.

Section TotalOrdDec.
  Context {A B} `{! TotalOrdDec A ,! TotalOrdDec B }.

  Definition sum_tord_dec (ab1:A+B) (ab2:A+B) : comparison :=
    match ab1,ab2 with
    | inl a1,inl a2 => a1 <=>! a2
    | inl _,inr _ => Lt
    | inr _,inl _ => Gt
    | inr b1,inr b2 => b1 <=>! b2
    end.

  Global Instance sum_TotalOrdDec : TotalOrdDec (A+B) := { tord_dec := sum_tord_dec }.
End TotalOrdDec.
Global Instance sum_Bif_TotalOrdDec : Bif_TotalOrdDec sum := { bif_total_ord_dec := @sum_TotalOrdDec }.

Section TotalOrd_RDC.
  Context {A B}
    `{! Lte A ,! Eqv A ,! ER_WF A ,! TotalOrd A ,! TotalOrdDec A ,! TotalOrd_RDC A
     ,! Lte B ,! Eqv B ,! ER_WF B ,! TotalOrd B ,! TotalOrdDec B ,! TotalOrd_RDC B
     }.

  Global Instance sum_TotalOrd_RDC : TotalOrd_RDC (A+B).
  Proof.
    Local Ltac mysimp :=
      match goal with
      | [ |- inl _ ~= inl _ ] => constructor
      | [ |- inr _ ~= inr _ ] => constructor
      | [ |- inl _ <= inr _ ] => constructor
      | [ |- inl _ < inl _ ] => apply InjectionRespect_eta
      | [ |- inl _ < inr _ ] => constructor
      | [ |- inr _ < inr _ ] => apply InjectionRespect_eta
      | [ |- _ <=>! _ = Eq ] => apply tord_rel_correct_eqv
      | [ |- _ <=>! _ = Lt ] => apply tord_rel_correct_lt
      | [ |- _ <=>! _ = Gt ] => apply tord_rel_correct_gt
      | [ H : inl _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ ~= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ ~= inr _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inr _ <= inl _ |- _ ] => inversion H ; subst ; clear H
      | [ H : inl _ < inl _ |- _ ] => apply InjectionRespect_beta in H
      | [ H : inr _ < inr _ |- _ ] => apply InjectionRespect_beta in H
      | [ H : inr _ < inl _ |- _ ] => destruct H
      | [ H : _ <=>! _ = Eq |- _ ] => apply tord_dec_correct_eqv in H
      | [ H : _ <=>! _ = Lt |- _ ] => apply tord_dec_correct_lt in H
      | [ H : _ <=>! _ = Gt |- _ ] => apply tord_dec_correct_gt in H
      | [ |- ~ inr _ <= inl _ ] => unfold "~" ; intros
      | _ => auto
      end.
    constructor ; intros ; destruct x,y ; simpl in * ; repeat mysimp ; try congruence.
  Qed.
End TotalOrd_RDC.
Global Instance sum_Bif_TotalOrd_RDC : Bif_TotalOrd_RDC sum := { bif_total_ord_rdc := @sum_TotalOrd_RDC }.

Section Lattice.
  Context {A B} `{! Lattice A ,! Lattice B }.

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
End Lattice.
Global Instance sum_Bif_Lattice : Bif_Lattice sum := { bif_lattice := @sum_Lattice }.

Section LatticeWF.
  Context {A B}
    `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! Lattice A ,! LatticeWF A
     ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B ,! Lattice B ,! LatticeWF B
     }.

  Global Instance sum_LatticeWF : LatticeWF (A+B).
  Proof.
    Local Ltac mysimp :=
      match goal with
      | [ |- and _ _ ] => constructor
      | [ |- inl _ <= inl _ ] => eapply InjectionRespect_eta
      | [ |- inl _ <= inr _ ] => constructor
      | [ |- inr _ <= inr _ ] => eapply InjectionRespect_eta
      | [ |- (?a /\ _) <= ?a ] => apply lmeet_ineq
      | [ |- (_ /\ ?a) <= ?a ] => apply lmeet_ineq
      | [ |- ?a <= (?a \/ _) ] => apply ljoin_ineq
      | [ |- ?a <= (_ \/ ?a) ] => apply ljoin_ineq
      | [ |- ?a <= ?a ] => reflexivity
      | _ => auto
      end.
    constructor ; intros ; destruct t1,t2 ; unfold "/\","\/" ; simpl ; repeat mysimp.
  Qed.
End LatticeWF.
Global Instance sum_Bif_LatticeWF : Bif_LatticeWF sum := { bif_lattice_wf := @sum_LatticeWF }.

Section BoundedLattice.
  Context {A B} `{! BoundedLattice A ,! BoundedLattice B }.

  Definition sum_top : A+B := inr ltop.
  Definition sum_bot : A+B := inl lbot.

  Global Instance sum_BoundedLattice : BoundedLattice (A+B) :=
    { ltop := sum_top
    ; lbot := sum_bot
    }.
End BoundedLattice.
Global Instance sum_Bif_BoundedLattice : Bif_BoundedLattice sum := { bif_bounded_lattice := @sum_BoundedLattice }.

Section BoundedLatticeWF.
  Global Instance sum_BoundedLatticeWF {A B}
    `{! Lte A ,! Eqv A ,! ER_WF A ,! PartialOrd A ,! Lattice A ,! BoundedLattice A ,! LatticeWF A ,! BoundedLatticeWF A
     ,! Lte B ,! Eqv B ,! ER_WF B ,! PartialOrd B ,! Lattice B ,! BoundedLattice B ,! LatticeWF B ,! BoundedLatticeWF B
     } : BoundedLatticeWF (A+B).
    constructor ; eauto with typeclass_instances ; intros.
    - destruct t ; constructor.
      apply ltop_ineq.
    - destruct t ; constructor.
      apply lbot_ineq.
  Qed.
End BoundedLatticeWF.
Global Instance sum_Bif_BoundedLatticeWF : Bif_BoundedLatticeWF sum := { bif_bounded_lattice_wf := @sum_BoundedLatticeWF }.
Require Import FP.Data.TwoThreeTrees.
Require Import FP.Structures.WellFormed.
Require Import FP.Data.N.
Require Import FP.Data.Unit.
Require Import FP.Data.Sum.
Require Import FP.Data.Ext.
Require Import FP.Structures.Peano.
Require Import FP.Structures.Lattice.
Require Import FP.Structures.Injection.
Require Import FP.Structures.Ord.
Require Import FP.Structures.Eqv.
Require Import FP.Structures.Additive.
Require Import FP.Structures.Alternative.
Require Import FP.Structures.Functor.
Require Import FP.Structures.Monad.
Require Import FP.Relations.RelDec.

Import MonadNotation.
Import NNotation.
Import EqvNotation.
Import OrdNotation.
Import AdditiveNotation.
Import AlternativeNotation.

Module TwoThreeTreesWF.
  Import TwoThreeTrees.

  Section Context.
    Context {K:Type}.
    Context {E:Eqv K} {EWF:EqvWF K}.
    Context {O:Ord K} {OWF:OrdWF K}.
    Context {L:Lattice K} {LWF:LatticeWF K}.
    Context {B:BoundedLattice K} {BWF:BoundedLatticeWF K}.
    Context {OD:OrdDec K} {ODC:OrdDecCorrect K}.
    Context {V:Type}.

    Inductive in_tree : K -> tree K V -> Prop :=
      | InTwoLeftTree :
          forall k tl pm tr,
            in_tree k tl -> in_tree k (Two_t tl pm tr)
      | InTwoRightTree :
          forall k tl pm tr,
            in_tree k tr -> in_tree k (Two_t tl pm tr)
      | InTwoNode :
          forall k tl km vm tr,
            k ~= km -> in_tree k (Two_t tl (km,vm) tr)
      | InThreeLeftTree :
          forall k tl pl tm pr tr,
            in_tree k tl -> in_tree k (Three_t tl pl tm pr tr)
      | InThreeMiddleTree :
          forall k tl pl tm pr tr,
            in_tree k tm -> in_tree k (Three_t tl pl tm pr tr)
      | InThreeRightTree :
          forall k tl pl tm pr tr,
            in_tree k tr -> in_tree k (Three_t tl pl tm pr tr)
      | InThreeLeftNode :
          forall k tl kl vl tm pr tr,
            k ~= kl -> in_tree k (Three_t tl (kl,vl) tm pr tr)
      | InThreeRightNode :
          forall k tl pl tm kr vr tr,
            k ~= kr -> in_tree k (Three_t tl pl tm (kr,vr) tr).
    Hint Constructors in_tree.
    Definition in_two_node_lib :
      forall tl km vm tr, in_tree km (Two_t tl (km,vm) tr).
    Proof. intros ; eapply InTwoNode ; reflexivity. Qed.
    Hint Resolve in_two_node_lib.
    Definition in_three_left_node_lib :
      forall tl kl vl tm pr tr,
        in_tree kl (Three_t tl (kl,vl) tm pr tr).
    Proof. intros ; eapply InThreeLeftNode ; reflexivity. Qed.
    Hint Resolve in_three_left_node_lib.
    Definition in_three_right_node_lib :
      forall tl pl tm kr vr tr,
        in_tree kr (Three_t tl pl tm (kr,vr) tr).
    Proof. intros ; eapply InThreeRightNode ; reflexivity. Qed.
    Hint Resolve in_three_right_node_lib.

    Inductive tree_iwf : ext_top_bot K -> ext_top_bot K -> N -> tree K V -> Prop :=
      | NullWF :
          forall
            t_lower_bound t_upper_bound,
              tree_iwf t_lower_bound t_upper_bound 0 Null_t
      | TwoWF :
          forall
            tl tl_lower_bound tl_upper_bound
            tr tr_lower_bound tr_upper_bound
            t_height
            km vm,
              tree_iwf tl_lower_bound tl_upper_bound t_height tl
           -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
           -> tl_upper_bound < inject km < tr_lower_bound
           -> tree_iwf tl_lower_bound tr_upper_bound (t_height+1)
                       (Two_t tl (km,vm) tr)
      | ThreeWF :
          forall
            tl tl_lower_bound tl_upper_bound
            tm tm_lower_bound tm_upper_bound
            tr tr_lower_bound tr_upper_bound
            t_height
            kl vl kr vr,
              tree_iwf tl_lower_bound tl_upper_bound t_height tl
           -> tree_iwf tm_lower_bound tm_upper_bound t_height tm
           -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
           -> tl_upper_bound < inject kl < tm_lower_bound
           -> tm_upper_bound < inject kr < tr_lower_bound
           -> tree_iwf tl_lower_bound tr_upper_bound (t_height+1)
                       (Three_t tl (kl,vl) tm (kr,vr) tr).
    Hint Constructors tree_iwf.

    Inductive in_context : K -> context K V -> Prop :=
      | InTwoLeftHoleContext :
          forall k pm tr c,
            in_context k c -> in_context k (TwoLeftHole_c pm tr c)
      | InTwoLeftHoleTree :
          forall k pm tr c,
            in_tree k tr -> in_context k (TwoLeftHole_c pm tr c)
      | InTwoLeftHoleNode :
          forall k km vm tr c,
            k ~= km -> in_context k (TwoLeftHole_c (km,vm) tr c)
      | InTwoRightHoleContext :
          forall k tl pm c,
            in_context k c -> in_context k (TwoRightHole_c tl pm c)
      | InTwoRightHoleTree :
          forall k tl pm c,
            in_tree k tl -> in_context k (TwoRightHole_c tl pm c)
      | InTwoRightHoleNode :
          forall k tl km vm c,
            k ~= km -> in_context k (TwoRightHole_c tl (km,vm) c)
      | InThreeLeftHoleContext :
          forall k pl tm pr tr c,
            in_context k c -> in_context k (ThreeLeftHole_c pl tm pr tr c)
      | InThreeLeftHoleMiddleTree :
          forall k pl tm pr tr c,
            in_tree k tm -> in_context k (ThreeLeftHole_c pl tm pr tr c)
      | InThreeLeftHoleRightTree :
          forall k pl tm pr tr c,
            in_tree k tr -> in_context k (ThreeLeftHole_c pl tm pr tr c)
      | InThreeLeftHoleLeftNode :
          forall k kl vl tm pr tr c,
            k ~= kl -> in_context k (ThreeLeftHole_c (kl,vl) tm pr tr c)
      | InThreeLeftHoleRightNode :
          forall k pl tm kr vr tr c,
            k ~= kr -> in_context k (ThreeLeftHole_c pl tm (kr,vr) tr c)
      | InThreeMiddleHoleContext :
          forall k tl pl pr tr c,
            in_context k c -> in_context k (ThreeMiddleHole_c tl pl pr tr c)
      | InThreeMiddleHoleLeftTree :
          forall k tl pl pr tr c,
            in_tree k tl -> in_context k (ThreeMiddleHole_c tl pl pr tr c)
      | InThreeMiddleHoleRightTree :
          forall k tl pl pr tr c,
            in_tree k tr -> in_context k (ThreeMiddleHole_c tl pl pr tr c)
      | InThreeMiddleHoleLeftNode :
          forall k tl kl vl pr tr c,
            k ~= kl -> in_context k (ThreeMiddleHole_c tl (kl,vl) pr tr c)
      | InThreeMiddleHoleRightNode :
          forall k tl pl kr vr tr c,
            k ~= kr -> in_context k (ThreeMiddleHole_c tl pl (kr,vr) tr c)
      | InThreeRightHoleContext :
          forall k tl pl tm pr c,
            in_context k c -> in_context k (ThreeRightHole_c tl pl tm pr c)
      | InThreeRightHoleLeftTree :
          forall k tl pl tm pr c,
            in_tree k tl -> in_context k (ThreeRightHole_c tl pl tm pr c)
      | InThreeRightHoleMiddleTree :
          forall k tl pl tm pr c,
            in_tree k tm -> in_context k (ThreeRightHole_c tl pl tm pr c)
      | InThreeRightHoleLeftNode :
          forall k tl kl vl tm pr c,
            k ~= kl -> in_context k (ThreeRightHole_c tl (kl,vl) tm pr c)
      | InThreeRightHoleRightNode :
          forall k tl pl tm kr vr c,
            k ~= kr -> in_context k (ThreeRightHole_c tl pl tm (kr,vr) c).
    Hint Constructors in_context.
            
    Inductive context_iwf
        : ext_top_bot K -> ext_top_bot K -> N (* bounds and height of hole *)
       -> ext_top_bot K -> ext_top_bot K -> N (* bounds and height when filled *)
       -> context K V
       -> Prop :=
      | TopWF :
          forall
            t_lower_bound t_upper_bound
            t_height,
              context_iwf t_lower_bound t_upper_bound t_height
                          t_lower_bound t_upper_bound t_height Top_c
      | TwoLeftHoleWF :
          forall
            h_lower_bound h_upper_bound h_height
            tr tr_lower_bound tr_upper_bound
            c c_lower_bound c_upper_bound c_height
            k v,
              context_iwf h_lower_bound tr_upper_bound (h_height+1)
                          c_lower_bound c_upper_bound c_height c
           -> tree_iwf tr_lower_bound tr_upper_bound h_height tr
           -> h_upper_bound < inject k < tr_lower_bound
           -> context_iwf h_lower_bound h_upper_bound h_height
                          c_lower_bound c_upper_bound c_height
                          (TwoLeftHole_c (k,v) tr c)
      | TwoRightHoleWF :
          forall
            h_lower_bound h_upper_bound h_height
            tl tl_lower_bound tl_upper_bound
            c c_lower_bound c_upper_bound c_height
            k v,
              context_iwf tl_lower_bound h_upper_bound (h_height+1)
                          c_lower_bound c_upper_bound c_height c
           -> tree_iwf tl_lower_bound tl_upper_bound h_height tl
           -> tl_upper_bound < inject k < h_lower_bound
           -> context_iwf h_lower_bound h_upper_bound h_height
                          c_lower_bound c_upper_bound c_height
                          (TwoRightHole_c tl (k,v) c)
      | ThreeLeftHoleWF :
          forall
            h_lower_bound h_upper_bound h_height
            tm tm_lower_bound tm_upper_bound
            tr tr_lower_bound tr_upper_bound
            c c_lower_bound c_upper_bound c_height
            kl vl kr vr,
              context_iwf h_lower_bound tr_upper_bound (h_height+1)
                          c_lower_bound c_upper_bound c_height c
           -> tree_iwf tm_lower_bound tm_upper_bound h_height tm
           -> tree_iwf tr_lower_bound tr_upper_bound h_height tr
           -> h_upper_bound < inject kl < tm_lower_bound
           -> tm_upper_bound < inject kr < tr_lower_bound
           -> context_iwf h_lower_bound h_upper_bound h_height
                          c_lower_bound c_upper_bound c_height
                          (ThreeLeftHole_c (kl,vl) tm (kr,vr) tr c)
      | ThreeMiddleHoleWF :
          forall
            h_lower_bound h_upper_bound h_height
            tl tl_lower_bound tl_upper_bound
            tr tr_lower_bound tr_upper_bound
            c c_lower_bound c_upper_bound c_height
            kl vl kr vr,
              context_iwf tl_lower_bound tr_upper_bound (h_height+1)
                          c_lower_bound c_upper_bound c_height c
           -> tree_iwf tl_lower_bound tl_upper_bound h_height tl
           -> tree_iwf tr_lower_bound tr_upper_bound h_height tr
           -> tl_upper_bound < inject kl < h_lower_bound
           -> h_upper_bound < inject kr < tr_lower_bound
           -> context_iwf h_lower_bound h_upper_bound h_height
                          c_lower_bound c_upper_bound c_height
                          (ThreeMiddleHole_c tl (kl,vl) (kr,vr) tr c)
      | ThreeRightHoleWF :
          forall
            h_lower_bound h_upper_bound h_height
            tl tl_lower_bound tl_upper_bound
            tm tm_lower_bound tm_upper_bound
            c c_lower_bound c_upper_bound c_height
            kl vl kr vr,
              context_iwf tl_lower_bound h_upper_bound (h_height+1)
                          c_lower_bound c_upper_bound c_height c
           -> tree_iwf tl_lower_bound tl_upper_bound h_height tl
           -> tree_iwf tm_lower_bound tm_upper_bound h_height tm
           -> tl_upper_bound < inject kl < tm_lower_bound
           -> tm_upper_bound < inject kr < h_lower_bound
           -> context_iwf h_lower_bound h_upper_bound h_height
                          c_lower_bound c_upper_bound c_height
                          (ThreeRightHole_c tl (kl,vl) tm (kr,vr) c).
    Hint Constructors context_iwf.

  Inductive in_location : K -> location K V -> Prop :=
    | InLocTwoHoleContext :
        forall k tl tr c,
          in_context k c -> in_location k (TwoHole_l tl tr c)
    | InLocTwoHoleLeftTree :
        forall k tl tr c,
          in_tree k tl -> in_location k (TwoHole_l tl tr c)
    | InLocTwoHoleRightTree :
        forall k tl tr c,
          in_tree k tr -> in_location k (TwoHole_l tl tr c)
    | InLocThreeLeftHoleContext :
        forall k tl tm pr tr c,
          in_context k c -> in_location k (ThreeLeftHole_l tl tm pr tr c)
    | InLocThreeLeftHoleLeftTree :
        forall k tl tm pr tr c,
          in_tree k tl -> in_location k (ThreeLeftHole_l tl tm pr tr c)
    | InLocThreeLeftHoleMiddleTree :
        forall k tl tm pr tr c,
          in_tree k tm -> in_location k (ThreeLeftHole_l tl tm pr tr c)
    | InLocThreeLeftHoleRightTree :
        forall k tl tm pr tr c,
          in_tree k tr -> in_location k (ThreeLeftHole_l tl tm pr tr c)
    | InLocThreeLeftHoleNode :
        forall k tl tm kr vr tr c,
          k ~= kr -> in_location k (ThreeLeftHole_l tl tm (kr,vr) tr c)
    | InLocThreeRightHoleContext :
        forall k tl pl tm tr c,
          in_context k c -> in_location k (ThreeRightHole_l tl pl tm tr c)
    | InLocThreeRightHoleLeftTree :
        forall k tl pl tm tr c,
          in_tree k tl -> in_location k (ThreeRightHole_l tl pl tm tr c)
    | InLocThreeRightHoleMiddleTree :
        forall k tl pl tm tr c,
          in_tree k tm -> in_location k (ThreeRightHole_l tl pl tm tr c)
    | InLocThreeRightHoleRightTree :
        forall k tl pl tm tr c,
          in_tree k tr -> in_location k (ThreeRightHole_l tl pl tm tr c)
    | InLocThreeRightHoleNode :
        forall k tl kl vl tm tr c,
          k ~= kl -> in_location k (ThreeRightHole_l tl (kl,vl) tm tr c).
  Hint Constructors in_location.

  Inductive location_iwf 
      : ext_top_bot K -> ext_top_bot K (* bounds of hole *)
     -> ext_top_bot K -> ext_top_bot K -> N (* bounds and height when filled *)
     -> location K V
     -> Prop :=
    | LocTwoHoleWF :
        forall
          t_height
          tl tl_lower_bound tl_upper_bound
          tr tr_lower_bound tr_upper_bound
          c c_lower_bound c_upper_bound c_height,
            tree_iwf tl_lower_bound tl_upper_bound t_height tl
         -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
         -> context_iwf tl_lower_bound tr_upper_bound (t_height+1)
                        c_lower_bound c_upper_bound c_height c
         -> location_iwf tl_upper_bound tr_lower_bound
                         c_lower_bound c_upper_bound c_height
                         (TwoHole_l tl tr c)
    | LocThreeLeftHoleWF :
        forall
          t_height
          tl tl_lower_bound tl_upper_bound
          tm tm_lower_bound tm_upper_bound
          tr tr_lower_bound tr_upper_bound
          c c_lower_bound c_upper_bound c_height
          kr vr,
            tree_iwf tl_lower_bound tl_upper_bound t_height tl
         -> tree_iwf tm_lower_bound tm_upper_bound t_height tm
         -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
         -> tm_upper_bound < inject kr < tr_lower_bound
         -> context_iwf tl_lower_bound tr_upper_bound (t_height+1)
                        c_lower_bound c_upper_bound c_height c
         -> location_iwf tl_upper_bound tm_lower_bound
                         c_lower_bound c_upper_bound c_height
                         (ThreeLeftHole_l tl tm (kr,vr) tr c)
    | LocThreeRightHoleWF :
        forall
          t_height
          tl tl_lower_bound tl_upper_bound
          tm tm_lower_bound tm_upper_bound
          tr tr_lower_bound tr_upper_bound
          c c_lower_bound c_upper_bound c_height
          kl vl,
            tree_iwf tl_lower_bound tl_upper_bound t_height tl
         -> tree_iwf tm_lower_bound tm_upper_bound t_height tm
         -> tree_iwf tr_lower_bound tr_upper_bound t_height tr
         -> tl_upper_bound < inject kl < tm_lower_bound
         -> context_iwf tl_lower_bound tr_upper_bound (t_height+1)
                        c_lower_bound c_upper_bound c_height c
         -> location_iwf tm_upper_bound tr_lower_bound
                         c_lower_bound c_upper_bound c_height
                         (ThreeRightHole_l tl (kl,vl) tm  tr c).
  Hint Constructors location_iwf.
            
  Global Instance tree_WellFormed : WellFormed (tree K V) :=
    { wf :=
        fun (t:tree K V) =>
          exists (n:N) (lb:ext_top_bot K) (ub:ext_top_bot K),
            tree_iwf lb ub n t
    }.

  Local Ltac mysimp :=
  match goal with
    | [ |- forall  _, _ ] => intros
    | [ |- _ /\ _ ] => constructor
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : inl _ = inr _ |- _ ] => discriminate H
    | [ H : inr _ = inr _ |- _ ] => inversion H ; subst ; clear H
    | [ H : ?a < ?b < ?c |- ?a < ?b ] => apply H
    | [ H : ?a < ?b < ?c |- ?b < ?c ] => apply H
    | [ H1 : ?X, H2 : ?X -> ?Y |- ?Y ] => apply (H2 H1)
    | [ |- match ?e with _ => _ end ] =>
        let x := fresh in
        remember e as x ; destruct x
    | [ H : forall c' k,
              (@?X c' k) c' k
           /\ (@?Y c' k) c' k
      |- _ ] =>
        let c' := fresh "c'" in
        let k := fresh "k" in
        let H1 := fresh in
        let H2 := fresh in
        assert (forall c' k, X c' k) as H1;
          [ intros c' k ; apply (proj1 (H c' k)) | idtac ] ;
        assert (forall c' k, Y c' k) as H2;
          [ intros c' k ; apply (proj2 (H c' k)) | idtac ] ;
        clear H ; simpl in H1 ; simpl in H2
    | [ |- context [ let (_,_) := ?p in _ ] ] => destruct p
    | [ H : context [ let (_,_) := ?p in _ ] |- _ ] => destruct p
    | [ H1 : ?x ~= ?z, H2 : ?y ~= ?z, H3 : ?x /~= ?y |- _ ] =>
        exfalso ; apply H3 ; transitivity z ; [ apply H1 | symmetry ; apply H2 ]
    | _ => auto
  end.

  Local Ltac rip :=
    match goal with
    | [ H : in_tree _ Null_t |- _ ] => inversion H
    | [ H : in_tree _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
    | [ H : in_tree _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
    | [ H : tree_iwf _ _ _ Null_t |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : tree_iwf _ _ _ (Two_t _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : tree_iwf _ _ _ (Three_t _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_context _ Top_c |- _ ] => inversion H
    | [ H : in_context _ (TwoLeftHole_c _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_context _ (TwoRightHole_c _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_context _ (ThreeLeftHole_c _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_context _ (ThreeMiddleHole_c _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_context _ (ThreeRightHole_c _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : context_iwf _ _ _ _ _ _ Top_c |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : context_iwf _ _ _ _ _ _ (TwoLeftHole_c _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : context_iwf _ _ _ _ _ _ (TwoRightHole_c _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : context_iwf _ _ _ _ _ _ (ThreeLeftHole_c _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : context_iwf _ _ _ _ _ _ (ThreeMiddleHole_c _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : context_iwf _ _ _ _ _ _ (ThreeRightHole_c _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_location _ (TwoHole_l _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_location _ (ThreeLeftHole_l _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : in_location _ (ThreeRightHole_l _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : location_iwf _ _ _ _ _ (TwoHole_l _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : location_iwf _ _ _ _ _ (ThreeLeftHole_l _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | [ H : location_iwf _ _ _ _ _ (ThreeRightHole_l _ _ _ _ _) |- _ ] =>
        inversion H ; subst ; clear H
    | _ => auto
    end.

  Opaque fplus fmap.

  Lemma locate_greatest_in :
    forall
      (t:tree K V) (c:context K V),
        match locate_greatest t c with
        | None => True
        | Some ((k,_),lM) =>
            let l :=
              match lM with
              | inl c => TwoHole_l Null_t Null_t c
              | inr (el,c) => ThreeRightHole_l Null_t el Null_t Null_t c
              end
            in
            forall k', k /~= k' ->
              (in_tree k' t -> in_location k' l)
           /\ (in_context k' c -> in_location k' l)
        end.
  Proof.
    intros t ; induction t ; intros.
    simpl ; auto.
    cbv beta iota delta [locate_greatest].
    fold (@locate_greatest K V).
  specialize (IHt2 (TwoRightHole_c t1 p c)).
  remember (locate_greatest t2 (TwoRightHole_c t1 p c)) as foo ; destruct foo.
  simpl.
  simpl.
  simp
  

  Lemma zip_in :
    forall (c:context K V) (t:tree K V) (k:K),
      (in_context k c -> in_tree k (zip t c))
   /\ (in_tree k t -> in_tree k (zip t c)).
  Proof.
    intros c ; induction c ; repeat mysimp ; repeat rip ; eauto.
  Qed.
  Lemma zip_in_context :
    forall (c:context K V) (t:tree K V) (k:K),
      in_context k c -> in_tree k (zip t c).
  Proof. apply zip_in. Qed.
  Hint Resolve zip_in_context.
  Lemma zip_in_tree :
    forall (c:context K V) (t:tree K V) (k:K),
      in_tree k t -> in_tree k (zip t c).
  Proof. apply zip_in. Qed.
  Hint Resolve zip_in_tree.

  Lemma zip_wf :
    forall 
      (c:context K V) (t:tree K V)
      t_lower_bound t_upper_bound t_height
      c_lower_bound c_upper_bound c_height,
        tree_iwf t_lower_bound t_upper_bound t_height t
     -> context_iwf t_lower_bound t_upper_bound t_height
                    c_lower_bound c_upper_bound c_height c
     -> tree_iwf c_lower_bound c_upper_bound c_height (zip t c).
  Proof.
    intros c ; induction c ; repeat mysimp ; repeat rip ; eapply IHc ; eauto.
  Qed.
  Hint Resolve zip_wf.

  Lemma fuse_in :
    forall (c1:context K V) (c2:context K V) k,
      (in_context k c1 -> in_context k (fuse c1 c2))
   /\ (in_context k c2 -> in_context k (fuse c1 c2)).
  Proof.
    intros c ; induction c ; simpl ; repeat mysimp ; repeat rip.
  Qed.
  Lemma fuse_in_context1 :
    forall (c1:context K V) (c2:context K V) k,
      in_context k c1 -> in_context k (fuse c1 c2).
  Proof. apply fuse_in. Qed.
  Hint Resolve fuse_in_context1.
  Lemma fuse_in_context2 :
    forall (c1:context K V) (c2:context K V) k,
      in_context k c2 -> in_context k (fuse c1 c2).
  Proof. apply fuse_in. Qed.
  Hint Resolve fuse_in_context2.

  Lemma fuse_wf :
    forall
      (c1:context K V) (c2:context K V)
      c1h_lower_bound c1h_upper_bound c1h_height
      c1_lower_bound c1_upper_bound c1_height
      c2_lower_bound c2_upper_bound c2_height,
        context_iwf c1h_lower_bound c1h_upper_bound c1h_height
                    c1_lower_bound c1_upper_bound c1_height c1
     -> context_iwf c1_lower_bound c1_upper_bound c1_height
                    c2_lower_bound c2_upper_bound c2_height c2
     -> context_iwf c1h_lower_bound c1h_upper_bound c1h_height
                    c2_lower_bound c2_upper_bound c2_height (fuse c1 c2).
  Proof.
    intros c1 ; induction c1 ; simpl ; repeat mysimp ; repeat rip ; eauto.
  Qed.
  Hint Resolve fuse_wf.

  Lemma fill_location_in :
    forall (l:location K V) (k:K) (v:V),
      (in_tree k (fill_location (k,v) l))
   /\ (forall k', in_location k' l -> in_tree k' (fill_location (k,v) l)).
  Proof.
    intros l ; induction l ; simpl ; repeat mysimp ; repeat rip.
  Qed.
  Lemma fill_location_in_filled :
    forall (l:location K V) (k:K) (v:V),
      in_tree k (fill_location (k,v) l).
  Proof. intros ; apply (proj1 (fill_location_in _ _ _)). Qed.
  Hint Resolve fill_location_in_filled.
  Lemma fill_location_in_tree :
    forall (l:location K V) (k:K) (v:V) (k':K),
      in_location k' l -> in_tree k' (fill_location (k,v) l).
  Proof. intros * * * * H ; apply (proj2 (fill_location_in _ _ _) _ H). Qed.
  Hint Resolve fill_location_in_tree.

  Lemma fill_location_wf :
    forall
      (l:location K V) (k:K) (v:V)
      h_lower_bound h_upper_bound
      c_lower_bound c_upper_bound c_height,
        h_lower_bound < inject k < h_upper_bound
     -> location_iwf h_lower_bound h_upper_bound
                     c_lower_bound c_upper_bound c_height l
     -> tree_iwf c_lower_bound c_upper_bound c_height (fill_location (k,v) l).
  Proof.
    intros l ; induction l ; intros ; repeat mysimp ; repeat rip ; eapply zip_wf ;
      eauto.
  Qed.
  Hint Resolve fill_location_wf.

  Lemma locate_in :
    forall (t:tree K V) (k:K) (c:context K V),
      match locate k t c with
      | inl c' =>
          forall k',
            (in_tree k' t -> in_context k' c')
         /\ (in_context k' c -> in_context k' c')
      | inr ((k',_),l) =>
          k ~= k'
       /\ (forall k'', k /~= k'' ->
             (in_tree k'' t -> in_location k'' l)
          /\ (in_context k'' c -> in_location k'' l))
      end.
  Proof.
    intros t ; induction t ; intros ; simpl ; repeat mysimp ; repeat rip ;
      repeat
        match goal with
        | [ H : context[ ?a <=>! ?b ] |- _ ] =>
            let cmp := fresh "cmp" in
            remember (a <=>! b) as cmp eqn:cmp_eqn ; symmetry in cmp_eqn ;
              destruct cmp as [cmp|cmp|cmp] ;
              [ apply ord_dec_correct_eqv in cmp_eqn
              | apply ord_dec_correct_lt in cmp_eqn
              | apply ord_dec_correct_gt in cmp_eqn
              ]
        | [ H : context[ ?a <=>! ?b ] |- _ ] =>
            let cmp := fresh "cmp" in
            remember (a <=>! b) as cmp eqn:cmp_eqn2 ; symmetry in cmp_eqn2 ;
              destruct cmp as [cmp|cmp|cmp] ;
              [ apply ord_dec_correct_eqv in cmp_eqn2
              | apply ord_dec_correct_lt in cmp_eqn2
              | apply ord_dec_correct_gt in cmp_eqn2
              ]
        | [ H1 : forall k c, match locate k ?t c with _ => _ end
          , H2 : _ = locate ?k ?t ?c
          |- _ ] =>
            specialize (H1 k c) ; rewrite <- H2 in H1
        | [ H : forall k, _ /\ _
          |- context[ ?k ]
          ] => specialize (H k)
        end ; repeat mysimp.
  Qed.

  Lemma locate_wf :
    forall
      (t:tree K V) (k:K) (c:context K V)
      t_lower_bound t_upper_bound t_height
      c_lower_bound c_upper_bound c_height,
        tree_iwf t_lower_bound t_upper_bound t_height t
     -> context_iwf t_lower_bound t_upper_bound t_height
                    c_lower_bound c_upper_bound c_height c
     -> exists h_lower_bound h_upper_bound,
          match locate k t c with
          | inl c =>
              context_iwf h_lower_bound h_upper_bound 0
                          c_lower_bound c_upper_bound c_height c
          | inr ((_,_),l) =>
              location_iwf h_lower_bound h_upper_bound
                           c_lower_bound c_upper_bound c_height l
          end.
  Proof.
    intros t ; induction t ; intros ; simpl ; repeat mysimp ; repeat rip ;
      repeat
        match goal with
        | [ |- context[ ?a <=>! ?b ] ] =>
            let cmp := fresh "cmp" in
            remember (a <=>! b) as cmp eqn:cmp_eqn ; symmetry in cmp_eqn ;
              destruct cmp as [cmp|cmp|cmp] ;
              [ apply ord_dec_correct_eqv in cmp_eqn
              | apply ord_dec_correct_lt in cmp_eqn
              | apply ord_dec_correct_gt in cmp_eqn
              ]
        | [ |- context[ ?a <=>! ?b ] ] =>
            let cmp := fresh "cmp" in
            remember (a <=>! b) as cmp eqn:cmp_eqn2 ; symmetry in cmp_eqn2 ;
              destruct cmp as [cmp|cmp|cmp] ;
              [ apply ord_dec_correct_eqv in cmp_eqn2
              | apply ord_dec_correct_lt in cmp_eqn2
              | apply ord_dec_correct_gt in cmp_eqn2
              ]
        end ; eauto.
  Qed.

          

  Lemma locate_greatest_wf :
    forall
      (t:tree K V) (c:context K V)
      t_lower_bound t_upper_bound t_height
      c_lower_bound c_upper_bound c_height,
        tree_iwf t_lower_bound t_upper_bound t_height
     -> context_iwf t_lower_bound t_upper_bound t_height
                    c_lower_bound c_upper_bound c_height c
     -> exists h_lower_bound h_upper_bound,
          match locate_greatest t c with
          | None => t = Null_t
          | Some l
  
End TwoThreeTreesWF.
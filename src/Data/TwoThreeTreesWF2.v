Require Import FP.CoreData.
Require Import FP.CoreClasses.
Require Import FP.Classes.
Require Import FP.Data.Sum.
Require Import FP.Data.Prod.
Require Import FP.Data.Option.
Require Import FP.Data.Extend.
Require Import FP.Data.TwoThreeTrees.

Import CoreClassesNotation.
Import CoreDataNotation.
Import ClassesNotation.


Module TwoThreeTreesWF.
  Import TwoThreeTrees.

  Section Context.
    Context {K V:Type}
      `{! Lte K ,! Eqv K ,! ER_WF K ,! TotalOrd K ,! TotalOrdDec K ,! TotalOrd_RDC K }.

    Inductive empty_tree : tree K V -> Prop :=
      | Empty_Null : empty_tree Null_t.
    Hint Constructors empty_tree.

    Inductive not_empty_tree : tree K V -> Prop :=
      | NotEmpty_Two : forall tl p tr, not_empty_tree (Two_t tl p tr)
      | NotEmtpy_Three : forall tl pl tm pr tr, not_empty_tree (Three_t tl pl tm pr tr).
    Hint Constructors not_empty_tree.
    
    Inductive in_tree : K -> tree K V -> Prop :=
      | In_TwoLeftTree :
          forall k tl pm tr, in_tree k tl -> in_tree k (Two_t tl pm tr)
      | In_TwoNode :
          forall k k' v tl tr, k ~= k' -> in_tree k (Two_t tl (k',v) tr)
      | In_TwoRightTree :
          forall k tl pm tr, in_tree k tr -> in_tree k (Two_t tl pm tr)
      | In_ThreeLeftTree :
          forall k tl pl tm pr tr, in_tree k tl -> in_tree k (Three_t tl pl tm pr tr)
      | In_ThreeLeftNode :
          forall k k' v tl tm pr tr, k ~= k' -> in_tree k (Three_t tl (k',v) tm pr tr)
      | In_ThreeMiddleTree :
          forall k tl pl tm pr tr, in_tree k tm -> in_tree k (Three_t tl pl tm pr tr)
      | In_ThreeRightNode :
          forall k k' v tl pl tm tr, k ~= k' -> in_tree k (Three_t tl pl tm (k',v) tr)
      | In_ThreeRightTree :
          forall k tl pl tm pr tr, in_tree k tr -> in_tree k (Three_t tl pl tm pr tr).
    Hint Constructors in_tree.

    Inductive not_in_tree : K -> tree K V -> Prop :=
      | NotIn_Null : forall k, not_in_tree k Null_t
      | NotIn_Two :
          forall k tl km vm tr,
          not_in_tree k tl
          -> k /~= km -> not_in_tree k tr
          -> not_in_tree k (Two_t tl (km,vm) tr)
      | NotIn_Three :
          forall k tl kl vl tm kr vr tr,
          not_in_tree k tl
          -> k /~= kl -> not_in_tree k tm
          -> k /~= kr -> not_in_tree k tr
          -> not_in_tree k (Three_t tl (kl,vl) tm (kr,vr) tr).
    Hint Constructors not_in_tree.

    Inductive maps_tree : K -> V -> tree K V -> Prop :=
      | Maps_TwoLeftTree :
          forall k v tl pm tr, maps_tree k v tl -> maps_tree k v (Two_t tl pm tr)
      | Maps_TwoNode :
          forall k k' v tl tr, k ~= k' -> maps_tree k v (Two_t tl (k',v) tr)
      | Maps_TwoRightTree :
          forall k v tl pm tr, maps_tree k v tr -> maps_tree k v (Two_t tl pm tr)
      | Maps_ThreeLeftTree :
          forall k v tl pl tm pr tr, maps_tree k v tl -> maps_tree k v (Three_t tl pl tm pr tr)
      | Maps_ThreeLeftNode :
          forall k k' v tl tm pr tr, k ~= k' -> maps_tree k v (Three_t tl (k',v) tm pr tr)
      | Maps_ThreeMiddleTree :
          forall k v tl pl tm pr tr, maps_tree k v tm -> maps_tree k v (Three_t tl pl tm pr tr)
      | Maps_ThreeRightNode :
          forall k k' v tl pl tm tr, k ~= k' -> maps_tree k v (Three_t tl pl tm (k',v) tr)
      | Maps_ThreeRightTree :
          forall k v tl pl tm pr tr, maps_tree k v tr -> maps_tree k v (Three_t tl pl tm pr tr).
    Hint Constructors maps_tree.

    Inductive bst_tree : extend K -> extend K -> tree K V -> Prop :=
      | BST_Null : forall l u, l <= u -> bst_tree l u Null_t
      | BST_Two :
          forall l_tl tl k v u_tr tr,
          bst_tree l_tl (Extend k) tl
          -> bst_tree (Extend k) u_tr tr
          -> bst_tree l_tl u_tr (Two_t tl (k,v) tr)
      | BST_Three :
          forall l_tl tl kl vl tm kr vr u_tr tr,
          bst_tree l_tl (Extend kl) tl
          -> bst_tree (Extend kl) (Extend kr) tm
          -> bst_tree (Extend kr) u_tr tr
          -> bst_tree l_tl u_tr (Three_t tl (kl,vl) tm (kr,vr) tr).
    Hint Constructors bst_tree.

    Inductive balance_tree : N -> tree K V -> Prop :=
      | Balance_Null : balance_tree 0 Null_t
      | Balance_Two :
          forall n tl p tr,
          balance_tree n tl
          -> balance_tree n tr
          -> balance_tree (n+1) (Two_t tl p tr)
      | Balance_Three :
          forall n tl pl tm pr tr,
          balance_tree n tl
          -> balance_tree n tm
          -> balance_tree n tr
          -> balance_tree (n+1) (Three_t tl pl tm pr tr).
    Hint Constructors balance_tree.

    Inductive in_context : K -> context K V -> Prop :=
      | In_TwoLeftHoleNode :
          forall k k' v tr c, k ~= k' -> in_context k (TwoLeftHole_c (k',v) tr c)
      | In_TwoLeftHoleTree :
          forall k pm tr c, in_tree k tr -> in_context k (TwoLeftHole_c pm tr c)
      | In_TwoLeftHoleContext :
          forall k pm tr c, in_context k c -> in_context k (TwoLeftHole_c pm tr c)
      | In_TwoRightHoleTree :
          forall k tl pm c, in_tree k tl -> in_context k (TwoRightHole_c tl pm c)
      | In_TwoRightHoleNode :
          forall k k' v tl c, k ~= k' -> in_context k (TwoRightHole_c tl (k',v) c)
      | In_TwoRightHoleContext :
          forall k tl pm c, in_context k c -> in_context k (TwoRightHole_c tl pm c)
      | In_ThreeLeftHoleLeftNode :
          forall k k' v tm pr tr c, k ~= k' -> in_context k (ThreeLeftHole_c (k',v) tm pr tr c)
      | In_ThreeLeftHoleMiddleTree :
          forall k pl tm pr tr c, in_tree k tm -> in_context k (ThreeLeftHole_c pl tm pr tr c)
      | In_ThreeLeftHoleRightNode :
          forall k k' v pl tm tr c, k ~= k' -> in_context k (ThreeLeftHole_c pl tm (k',v) tr c)
      | In_ThreeLeftHoleRightTree :
          forall k pl tm pr tr c, in_tree k tr -> in_context k (ThreeLeftHole_c pl tm pr tr c)
      | In_ThreeLeftHoleContext :
          forall k pl tm pr tr c, in_context k c -> in_context k (ThreeLeftHole_c pl tm pr tr c)
      | In_ThreeMiddleHoleLeftTree :
          forall k tl pl pr tr c, in_tree k tl -> in_context k (ThreeMiddleHole_c tl pl pr tr c)
      | In_ThreeMiddleHoleLeftNode :
          forall k k' v tl pr tr c, k ~= k' -> in_context k (ThreeMiddleHole_c tl (k',v) pr tr c)
      | In_ThreeMiddleHoleRightNode :
          forall k k' v tl pl tr c, k ~= k' -> in_context k (ThreeMiddleHole_c tl pl (k',v) tr c)
      | In_ThreeMiddleHoleRightTree :
          forall k tl pl pr tr c, in_tree k tr -> in_context k (ThreeMiddleHole_c tl pl pr tr c)
      | In_ThreeMiddleHoleContext :
          forall k tl pl pr tr c, in_context k c -> in_context k (ThreeMiddleHole_c tl pl pr tr c)
      | In_ThreeRightHoleLeftTree :
          forall k tl pl tm pr c, in_tree k tl -> in_context k (ThreeRightHole_c tl pl tm pr c)
      | In_ThreeRightHoleLeftNode :
          forall k k' v tl tm pr c, k ~= k' -> in_context k (ThreeRightHole_c tl (k',v) tm pr c)
      | In_ThreeRightHoleMiddleTree :
          forall k tl pl tm pr c, in_tree k tm -> in_context k (ThreeRightHole_c tl pl tm pr c)
      | In_ThreeRightHoleRightNode :
          forall k v tl pl tm c, in_context k (ThreeRightHole_c tl pl tm (k,v) c)
      | In_ThreeRightHoleContext :
          forall k tl pl tm pr c, in_context k c -> in_context k (ThreeRightHole_c tl pl tm pr c).
    Hint Constructors in_context.

    Inductive not_in_context : K -> context K V -> Prop :=
      | NotIn_Top : forall k, not_in_context k Top_c
      | NotIn_TwoLeftHole :
          forall k km vm tr c,
          k /~= km -> not_in_tree k tr
          -> not_in_context k c
          -> not_in_context k (TwoLeftHole_c (km,vm) tr c)
      | NotIn_TwoRightHole :
          forall k tl km vm c,
          not_in_tree k tl
          -> k /~= km -> not_in_context k c
          -> not_in_context k (TwoRightHole_c tl (km,vm) c)
      | NotIn_ThreeLeftHole :
          forall k kl vl tm kr vr tr c,
          k /~= kl -> not_in_tree k tm
          -> k /~= kr -> not_in_tree k tr
          -> not_in_context k c
          -> not_in_context k (ThreeLeftHole_c (kl,vl) tm (kr,vr) tr c)
      | NotIn_ThreeMiddleHole :
          forall k tl kl vl kr vr tr c,
          not_in_tree k tl
          -> k /~= kl
          -> k /~= kr -> not_in_tree k tr
          -> not_in_context k c
          -> not_in_context k (ThreeMiddleHole_c tl (kl,vl) (kr,vr) tr c)
      | NotIn_ThreeRightHole :
          forall k tl kl vl tm kr vr c,
          not_in_tree k tl
          -> k /~= kl -> not_in_tree k tm
          -> k /~= kr -> not_in_context k c
          -> not_in_context k (ThreeRightHole_c tl (kl,vl) tm (kr,vr) c).
    Hint Constructors not_in_context.
    (*
    Hint Extern 1 =>
      match goal with
      | [ |- not_in_context _ (TwoLeftHole_c ?p _ _) ] =>
           match p with (_,_) => fail | _ => destruct p end
      | [ |- not_in_context _ (TwoRightHole_c _ ?p _) ] =>
           match p with (_,_) => fail | _ => destruct p end
      | [ |- not_in_context _ (ThreeLeftHole_c ?p _ _ _ _) ] =>
           match p with (_,_) => fail | _ => destruct p end
      | [ |- not_in_context _ (ThreeLeftHole_c _ _ ?p _ _) ] =>
           match p with (_,_) => fail | _ => destruct p end
      | [ |- not_in_context _ (ThreeMiddleHole_c _ ?p _ _ _) ] =>
           match p with (_,_) => fail | _ => destruct p end
      | [ |- not_in_context _ (ThreeMiddleHole_c _ _ ?p _ _) ] =>
           match p with (_,_) => fail | _ => destruct p end
      | [ |- not_in_context _ (ThreeRightHole_c _ ?p _ _ _) ] =>
           match p with (_,_) => fail | _ => destruct p end
      | [ |- not_in_context _ (ThreeRightHole_c _ _ _ ?p _) ] =>
           match p with (_,_) => fail | _ => destruct p end
      end.
*)

    Inductive maps_context : K -> V -> context K V -> Prop :=
      | Maps_TwoLeftHoleNode :
          forall k k' v tr c, k ~= k' -> maps_context k v (TwoLeftHole_c (k',v) tr c)
      | Maps_TwoLeftHoleTree :
          forall k v pm tr c, maps_tree k v tr -> maps_context k v (TwoLeftHole_c pm tr c)
      | Maps_TwoLeftHoleContext :
          forall k v pm tr c, maps_context k v c -> maps_context k v (TwoLeftHole_c pm tr c)
      | Maps_TwoRightHoleTree :
          forall k v tl pm c, maps_tree k v tl -> maps_context k v (TwoRightHole_c tl pm c)
      | Maps_TwoRightHoleNode :
          forall k k' v tl c, k ~= k' -> maps_context k v (TwoRightHole_c tl (k',v) c)
      | Maps_TwoRightHoleContext :
          forall k v tl pm c, maps_context k v c -> maps_context k v (TwoRightHole_c tl pm c)
      | Maps_ThreeLeftHoleLeftNode :
          forall k k' v tm pr tr c, k ~= k' -> maps_context k v (ThreeLeftHole_c (k',v) tm pr tr c)
      | Maps_ThreeLeftHoleMiddleTree :
          forall k v pl tm pr tr c, maps_tree k v tm -> maps_context k v (ThreeLeftHole_c pl tm pr tr c)
      | Maps_ThreeLeftHoleRightNode :
          forall k k' v pl tm tr c, k ~= k' -> maps_context k v (ThreeLeftHole_c pl tm (k',v) tr c)
      | Maps_ThreeLeftHoleRightTree :
          forall k v pl tm pr tr c, maps_tree k v tr -> maps_context k v (ThreeLeftHole_c pl tm pr tr c)
      | Maps_ThreeLeftHoleContext :
          forall k v pl tm pr tr c, maps_context k v c -> maps_context k v (ThreeLeftHole_c pl tm pr tr c)
      | Maps_ThreeMiddleHoleLeftTree :
          forall k v tl pl pr tr c, maps_tree k v tl -> maps_context k v (ThreeMiddleHole_c tl pl pr tr c)
      | Maps_ThreeMiddleHoleLeftNode :
          forall k k' v tl pr tr c, k ~= k' -> maps_context k v (ThreeMiddleHole_c tl (k',v) pr tr c)
      | Maps_ThreeMiddleHoleRightNode :
          forall k k' v tl pl tr c, k ~= k' -> maps_context k v (ThreeMiddleHole_c tl pl (k',v) tr c)
      | Maps_ThreeMiddleHoleRightTree :
          forall k v tl pl pr tr c, maps_tree k v tr -> maps_context k v (ThreeMiddleHole_c tl pl pr tr c)
      | Maps_ThreeMiddleHoleContext :
          forall k v tl pl pr tr c, maps_context k v c -> maps_context k v (ThreeMiddleHole_c tl pl pr tr c)
      | Maps_ThreeRightHoleLeftTree :
          forall k v tl pl tm pr c, maps_tree k v tl -> maps_context k v (ThreeRightHole_c tl pl tm pr c)
      | Maps_ThreeRightHoleLeftNode :
          forall k k' v tl tm pr c, k ~= k' -> maps_context k v (ThreeRightHole_c tl (k',v) tm pr c)
      | Maps_ThreeRightHoleMiddleTree :
          forall k v tl pl tm pr c, maps_tree k v tm -> maps_context k v (ThreeRightHole_c tl pl tm pr c)
      | Maps_ThreeRightHoleRightNode :
          forall k v tl pl tm c, maps_context k v (ThreeRightHole_c tl pl tm (k,v) c)
      | Maps_ThreeRightHoleContext :
          forall k v tl pl tm pr c, maps_context k v c -> maps_context k v (ThreeRightHole_c tl pl tm pr c).
    Hint Constructors maps_context.

    Inductive bst_context l_r u_r : extend K -> extend K -> context K V -> Prop :=
      | BST_Top : bst_context l_r u_r l_r u_r Top_c
      | BST_TwoLeftHole :
          forall l_c u_tr km vm tr c,
          bst_tree (Extend km) u_tr tr
          -> bst_context l_r u_r l_c u_tr c
          -> bst_context l_r u_r l_c (Extend km) (TwoLeftHole_c (km,vm) tr c)
      | BST_TwoRightHole :
          forall l_tl u_c tl km vm c,
          bst_tree l_tl (Extend km) tl
          -> bst_context l_r u_r l_tl u_c c
          -> bst_context l_r u_r (Extend km) u_c (TwoRightHole_c tl (km,vm) c)
      | BST_ThreeLeftHole :
          forall l_c u_tr kl vl tm kr vr tr c,
          bst_tree (Extend kl) (Extend kr) tm
          -> bst_tree (Extend kr) u_tr tr
          -> bst_context l_r u_r l_c u_tr c
          -> bst_context l_r u_r l_c (Extend kl) (ThreeLeftHole_c (kl,vl) tm (kr,vr) tr c)
      | BST_ThreeMiddleHole :
          forall l_tl u_tr tl kl vl kr vr tr c,
          bst_tree l_tl (Extend kl) tl
          -> bst_tree (Extend kr) u_tr tr
          -> bst_context l_r u_r l_tl u_tr c
          -> bst_context l_r u_r (Extend kl) (Extend kr) (ThreeMiddleHole_c tl (kl,vl) (kr,vr) tr c)
      | BST_ThreeRightHole :
          forall l_tl u_c tl kl vl tm kr vr c,
          bst_tree l_tl (Extend kl) tl
          -> bst_tree (Extend kl) (Extend kr) tm
          -> bst_context l_r u_r l_tl u_c c
          -> bst_context l_r u_r (Extend kr) u_c (ThreeRightHole_c tl (kl,vl) tm (kr,vr) c).
    Hint Constructors bst_context.

    Inductive balance_context : N -> N -> context K V -> Prop :=
      | Balance_Top : forall n, balance_context n n Top_c
      | Balance_TwoLeftHole :
          forall n n' pm tr c,
          balance_tree n tr
          -> balance_context (n+1) n' c
          -> balance_context n n' (TwoLeftHole_c pm tr c)
     | Balance_TwoRightHole :
         forall n n' tl pm c,
         balance_tree n tl
         -> balance_context (n+1) n' c
         -> balance_context n n' (TwoRightHole_c tl pm c)
     | Balance_ThreeLeftHole :
         forall n n' pl tm pr tr c,
         balance_tree n tm
         -> balance_tree n tr
         -> balance_context (n+1) n' c
         -> balance_context n n' (ThreeLeftHole_c pl tm pr tr c)
     | Balance_ThreeMiddleHole :
         forall n n' tl pl pr tr c,
         balance_tree n tl
         -> balance_tree n tr
         -> balance_context (n+1) n' c
         -> balance_context n n' (ThreeMiddleHole_c tl pl pr tr c)
     | Balance_ThreeRightHole :
         forall n n' tl pl tm pr c,
         balance_tree n tl
         -> balance_tree n tm
         -> balance_context (n+1) n' c
         -> balance_context n n' (ThreeRightHole_c tl pl tm pr c).
    Hint Constructors balance_context.
         
    Inductive in_location : K -> location K V -> Prop :=
      | In_LocTwoHoleLeftTree :
          forall k tl tr c, in_tree k tl -> in_location k (TwoHole_l tl tr c)
      | In_LocTwoHoleRightTree :
          forall k tl tr c, in_tree k tr -> in_location k (TwoHole_l tl tr c)
      | In_LocTwoHoleContext :
          forall k tl tr c, in_context k c -> in_location k (TwoHole_l tl tr c)
      | In_LocThreeLeftHoleLeftTree :
          forall k tl tm pr tr c, in_tree k tl -> in_location k (ThreeLeftHole_l tl tm pr tr c)
      | In_LocThreeLeftHoleMiddleTree :
          forall k tl tm pr tr c, in_tree k tm -> in_location k (ThreeLeftHole_l tl tm pr tr c)
      | In_LocThreeLeftHoleNode :
          forall k k' v tl tm tr c, k ~= k' -> in_location k (ThreeLeftHole_l tl tm (k',v) tr c)
      | In_LocThreeLeftHoleRightTree :
          forall k tl tm pr tr c, in_tree k tr -> in_location k (ThreeLeftHole_l tl tm pr tr c)
      | In_LocThreeLeftHoleContext :
          forall k tl tm pr tr c, in_context k c -> in_location k (ThreeLeftHole_l tl tm pr tr c)
      | In_LocThreeRightHoleLeftTree :
          forall k tl pl tm tr c, in_tree k tl -> in_location k (ThreeRightHole_l tl pl tm tr c)
      | In_LocThreeRightHoleNode :
          forall k k' v tl tm tr c, k ~= k' -> in_location k (ThreeRightHole_l tl (k',v) tm tr c)
      | In_LocThreeRightHoleMiddleTree :
          forall k tl pl tm tr c, in_tree k tm -> in_location k (ThreeRightHole_l tl pl tm tr c)
      | In_LocThreeRightHoleRightTree :
          forall k tl pl tm tr c, in_tree k tr -> in_location k (ThreeRightHole_l tl pl tm tr c)
      | In_LocThreeRightHoleContext :
          forall k tl pl tm tr c, in_context k c -> in_location k (ThreeRightHole_l tl pl tm tr c).
    Hint Constructors in_location.

    Inductive not_in_location : K -> location K V -> Prop :=
      | NotIn_TwoNode :
          forall k tl tr c,
          not_in_tree k tl
          -> not_in_tree k tr
          -> not_in_context k c
          -> not_in_location k (TwoHole_l tl tr c)
      | NotIn_ThreeLeftNode :
          forall k tl tm kr vr tr c,
          not_in_tree k tl
          -> not_in_tree k tm
          -> k /~= kr -> not_in_tree k tr
          -> not_in_context k c
          -> not_in_location k (ThreeLeftHole_l tl tm (kr,vr) tr c)
      | NotIn_ThreeRightNode :                   
          forall k tl kl vl tm tr c,
          not_in_tree k tl
          -> k /~= kl -> not_in_tree k tm
          -> not_in_tree k tr
          -> not_in_context k c
          -> not_in_location k (ThreeRightHole_l tl (kl,vl) tm  tr c).
    Hint Constructors not_in_location.

    Inductive bst_location l_r u_r : extend K -> location K V -> Prop :=
      | BST_TwoHole :
          forall kM l_c u_c tl tr c,
          bst_tree l_c kM tl
          -> bst_tree kM u_c tr
          -> bst_context l_r u_r l_c u_c c
          -> bst_location l_r u_r kM (TwoHole_l tl tr c)
      | BST_ThreeLeftNodeHole :
          forall kM l_c u_c tl tm kr vr tr c,
          bst_tree l_c kM tl
          -> bst_tree kM (Extend kr) tm
          -> bst_tree (Extend kr) u_c tr
          -> bst_context l_r u_r l_c u_c c
          -> bst_location l_r u_r kM (ThreeLeftHole_l tl tm (kr,vr) tr c)
      | BST_ThreeRightNodeHole :
          forall kM l_c u_c tl kl vl tm tr c,
          bst_tree l_c (Extend kl) tl
          -> bst_tree (Extend kl) kM tm
          -> bst_tree kM u_c tr
          -> bst_context l_r u_r l_c u_c c
          -> bst_location l_r u_r kM (ThreeRightHole_l tl (kl,vl) tm tr c).
    Hint Constructors bst_location.

    Inductive balance_location : N -> location K V -> Prop :=
      | Balance_TwoHole :
          forall n tl tr n' c,
          balance_tree n tl
          -> balance_tree n tr
          -> balance_context (n+1) n' c
          -> balance_location n' (TwoHole_l tl tr c)
      | Balance_ThreeLeftNodeHole :
          forall n tl tm pr tr n' c,
          balance_tree n tl
          -> balance_tree n tm
          -> balance_tree n tr
          -> balance_context (n+1) n' c
          -> balance_location n' (ThreeLeftHole_l tl tm pr tr c)
      | Balance_ThreeRightNodeHole :
          forall n tl pl tm tr n' c,
          balance_tree n tl
          -> balance_tree n tm
          -> balance_tree n tr
          -> balance_context (n+1) n' c
          -> balance_location n' (ThreeRightHole_l tl pl tm tr c).

    Local Ltac gd x := generalize dependent x.

    Lemma plus_one_elim : forall {x y}, x+1 = y+1 -> x=y.
    Proof.
      intros.
      assert (1+x=y+1).
      { transitivity (x+1) ; auto.
        symmetry.
        apply (BinNat.N.add_comm x 1).
      }
      assert (1+x=1+y).
      { transitivity (y+1) ; auto.
        apply (BinNat.N.add_comm y 1).
      }
      exact (BinNat.Nplus_reg_l 1 x y H1).
    Qed.
    Hint Immediate plus_one_elim.

    Lemma plus_one_not_zero_l : forall {n}, 0 = n+1 -> False.
    Admitted.
    (*
    Proof.
      intros n Heq ; destruct n ; unfold "+" in * ; simpl in * ; discriminate Heq.
    Qed.
    *)

    Lemma plus_one_not_zero_r : forall {n}, n+1 = 0 -> False.
    Admitted.
    (*
    Proof.
      intros n H ; symmetry in H ; eauto.
    Qed.
    *)

    Ltac exfalso_plus_one_not_zero :=
      match goal with
      | [ H : 0 = _ + 1 |- _ ] => exfalso ; apply (plus_one_not_zero_l H)
      | [ H : _ + 1 = 0 |- _ ] => exfalso ; apply (plus_one_not_zero_r H)
      end.
    Hint Extern 0 => exfalso_plus_one_not_zero.
                      
    Local Ltac mysimp :=
      match goal with
      (* basic rules *)
      | [ H : and _ _ |- _ ] => destruct H
      | [ H : exists _, _ |- _ ] => destruct H
      | [ H : ?x /\ _ |- _ ] => match type of x with Prop => destruct H | _ => fail end
      | [ H : _ <-> _ |- _ ] => destruct H
      | [ H1 : ?X , H2 : ?X -> exists _, _ |- _ ] => specialize (H2 H1) ; destruct H2
      | [ H : Lt = _ <=>! _ |- _ ] => symmetry in H ; apply tord_dec_correct_lt in H
      | [ H : Eq = _ <=>! _ |- _ ] => symmetry in H ; apply tord_dec_correct_eqv in H
      | [ H : Gt = _ <=>! _ |- _ ] => symmetry in H ; apply tord_dec_correct_gt in H
      | [ H1 : ?X -> ~?Y , H2 : ?X , H3 : ?Y |- _ ] => exfalso ; apply (H1 H2 H3)

      (* tree rules *)
      | [ |- bst_tree _ _ (Two_t _ _ _) ] => constructor
      | [ |- bst_tree _ _ (Three_t _ _ _ _ _) ] => constructor
      | [ |- not_in_tree _ Null_t ] => constructor
      | [ |- not_in_tree _ (Two_t _ (_,_) _) ] => constructor
      | [ |- not_in_tree _ (Two_t _ ?p _) ] => destruct p ; constructor
      | [ |- not_in_tree _ (Three_t _ (_,_) _ (_,_) _) ] => constructor
      | [ |- not_in_tree _ (Three_t _ ?p _ (_,_) _) ] => destruct p ; constructor
      | [ |- not_in_tree _ (Three_t _ (_,_) _ ?p _) ] => destruct p ; constructor
      | [ |- not_in_tree _ (Three_t _ ?pl _ ?pr _) ] => destruct pl,pr ; constructor
      | [ H : in_tree _ Null_t |- _ ] => inversion H
      | [ H : not_in_tree _ Null_t |- _ ] => inversion H ; subst ; clear H
      | [ H : not_in_tree _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : not_in_tree _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : maps_tree _ _ Null_t |- _ ] => inversion H
      | [ H : bst_tree _ _ Null_t |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_tree _ _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_tree _ _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_tree _ Null_t |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_tree _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_tree _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_tree 0 _ |- _ ] => inversion H ; subst ; clear H ; try exfalso_plus_one_not_zero
      | [ H : in_context _ Top_c |- _ ] => inversion H
      | [ H : in_context _ _ _ _ (ThreeLeftHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ _ _ _ (ThreeMiddleHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ _ _ _ (ThreeRightHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_context _ _ _ _ Top_c |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_context _ _ _ _ (TwoLeftHole_c _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_context _ _ _ _ (TwoRightHole_c _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_context _ _ _ _ (ThreeLeftHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_context _ _ _ _ (ThreeMiddleHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_context _ _ _ _ (ThreeRightHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_context _ _ Top_c |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_context _ _ (TwoLeftHole_c _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_context _ _ (TwoRightHole_c _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_context _ _ (ThreeLeftHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_context _ _ (ThreeMiddleHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_context _ _ (ThreeRightHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_location _ _ _ (TwoHole_l _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_location _ _ _ (ThreeLeftHole_l _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : bst_location _ _ _ (ThreeRightHole_l _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_location _ (TwoHole_l _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_location _ (ThreeLeftHole_l _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : balance_location _ (ThreeRightHole_l _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      end.

    Local Ltac rip :=
      match goal with
      (* basic rules *)
      | [ |- and _ _ ] => constructor
      | [ H : or _ _ |- _ ] => inversion H ; subst ; clear H
      | [ |- ~ _ ] => unfold "~" at 1 ; intros

      (* arithmatic rules *)
      | [ H : ?x+1 = ?y+1 |- _ ] => apply plus_one_elim in H ; subst x

      (* tree rules *)
      | [ H : in_tree _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_tree _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : maps_tree _ _ (Two_t _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : maps_tree _ _ (Three_t _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ (TwoLeftHole_c _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ (TwoRightHole_c _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ (ThreeLeftHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ (ThreeMiddleHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      | [ H : in_context _ (ThreeRightHole_c _ _ _ _ _) |- _ ] => inversion H ; subst ; clear H
      end.

    Create HintDb forward_db.
    Create HintDb backward_db.

    Ltac flip_eqn x :=
      match goal with
      | [ H : _ = ?E |- _ ] => match E with context [ x ] => symmetry in H end
      end.

    Ltac let_pair_drill :=
      match goal with
      | [ |- context [ let (_,_) := ?p in _ ] ] => destruct p
      | [ H : context [ let (_,_) := ?p in _ ] |- _ ] => destruct p
      end.

    Ltac tord_drill :=
      match goal with
      | [ |- context [?x <=>! ?y] ] =>
          let m := fresh "tord" in remember (x <=>! y) as m ; destruct m
      end.

    Ltac atom_match_drill :=
      match goal with
      | [ |- context [ match ?X with _ => _ end ] ] =>
          match X with (?f _) => fail 1 | _ => destruct X end
      | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
          match X with (?f _) => fail 1 | _ => destruct X end
      end.
    (*
      match goal with
      | [ |- context [ match ?x with _ => _ end ] ] =>
          match type of x with
          | (tree K V) => destruct x
          | (context K V) => destruct x
          | (location K V) => destruct x
          end
      | [ H : context [ match ?x with _ => _ end ] |- _ ] =>
          match type of x with
          | (tree K V) => destruct x
          | (context K V) => destruct x
          | (location K V) => destruct x
          end
      end.
  *)

    Lemma lt_eqv_contradiction : forall {x y}, x < y -> x /~= y.
    Admitted.
    (*
    Proof.
      intros x y Hlt Heqv ; apply Hlt ; refine (PartialOrd_respect_eqv y y _ y x _ _)
      ; try reflexivity ; symmetry ; auto.
    Qed.
    *)
    Hint Immediate lt_eqv_contradiction.

    Lemma lt_eqv_contradiction' : forall {x y}, x < y -> y /~= x.
    Admitted.
    (*
    Proof.
      intros x y Hlt Heqv ; apply Hlt ; refine (PartialOrd_respect_eqv y y _ y x _ _)
      ; try reflexivity ; auto.
    Qed.
    *)
    Hint Immediate lt_eqv_contradiction'.

    Lemma bst_null_lib : forall {m}, bst_tree m m Null_t.
    Admitted.
    (*
    Proof.
      intros ; econstructor ; reflexivity.
    Qed.
    *)
    Hint Immediate bst_null_lib.

    Lemma empty_balance : forall {t}, empty_tree t -> balance_tree 0 t.
    Proof.
      intros t H ; inversion H ; eauto.
    Qed.
    Hint Resolve empty_balance.

    Lemma balance_tree_unique : forall {n n' t}, balance_tree n t -> balance_tree n' t -> n = n'.
    Proof.
      intros n n' t ; gd n' ; gd n ; induction t ; intros ; repeat mysimp || rip ; eauto.
      rewrite (IHt1 _ _ H3 H4) ; auto.
      rewrite (IHt1 _ _ H4 H5) ; auto.
    Qed.
    Ltac balance_tree_unique_zero :=
      match goal with
      | [ Hemp : empty_tree ?t , Hbal : balance_tree ?n ?t |- _ ] =>
          match n with
          | 0 => fail
          | _ => assert (n = 0) ; [ eapply (balance_tree_unique Hbal) ; clear Hbal | subst ]
          end
      end.
    Hint Extern 1 => balance_tree_unique_zero.

    Lemma balance_tree_two_right_matches_left :
      forall {n tl tr n' c},
      balance_tree n tl -> balance_location n' (TwoHole_l tl tr c) -> balance_tree n tr.
    Proof.
      intros. inversion H0 ; subst ; clear H0.
      rewrite (balance_tree_unique H H5) ; auto.
    Qed.
    Hint Resolve balance_tree_two_right_matches_left.

    Lemma maps_to_in : forall {k t v}, maps_tree k v t -> in_tree k t.
    Admitted.
    (* 
    Proof.
      intros k t v H ; induction t ; repeat mysimp || rip ; eauto.
    Qed.
    *)
    Hint Resolve maps_to_in.

    Lemma in_to_maps : forall {k t}, in_tree k t -> exists v, maps_tree k v t.
    Admitted.
    (*
    Proof.
      intros k t H ; induction t ; repeat mysimp || rip ; eauto.
    Qed.
    *)

    (*
    Lemma not_in_to_neg_in_tree_two_node :
      forall k tl km vm tr, ~in_tree k (Two_t tl (km,vm) tr) -> k /~= km.
    Admitted.
    (*
    Proof. intros ; unfold "/~=" ; simpl ; unfold "~" ; intros ; apply H ; eauto. Qed.
    Hint Immediate not_in_to_neg_in_tree_two_node.
    *)
    *)

    (*
    Lemma not_in_to_neg_in_tree_three_left_node :
      forall k tl kl vl tm kr vr tr, ~in_tree k (Three_t tl (kl,vl) tm (kr,vr) tr) -> k /~= kl.
    Admitted.
    (*
    Proof. intros ; unfold "/~=" ; simpl ; unfold "~" ; intros ; apply H ; eauto. Qed.
    Hint Immediate not_in_to_neg_in_tree_three_left_node.
    *)
    *)

    (*
    Lemma not_in_to_neg_in_tree_three_right_node :
      forall k tl kl vl tm kr vr tr, ~in_tree k (Three_t tl (kl,vl) tm (kr,vr) tr) -> k /~= kr.
    Admitted.
    (*
    Proof. intros ; unfold "/~=" ; simpl ; unfold "~" ; intros ; apply H ; eauto. Qed.
    Hint Immediate not_in_to_neg_in_tree_three_right_node.
    *)
    *)

    Lemma not_in_to_neg_in_tree : forall k t, not_in_tree k t <-> ~in_tree k t.
    Admitted.
    (*
    Proof. intros ; induction t ; constructor ; intros ; repeat mysimp || rip ; eauto.  Qed.
    *)

    Lemma in_tree_dp : forall k t, in_tree k t \/ not_in_tree k t.
    Admitted.
    (*
    Proof.
      intros k t ; induction t ; repeat mysimp || rip || auto ; eauto.
      - destruct p as [k' v].
        remember (k <=>! k') as m ; destruct m ; repeat mysimp ; eauto
        ; right ; repeat mysimp || rip || auto ; eauto.
      - destruct p as [k' v], p0 as [k0' v0].
        remember (k <=>! k') as m ; destruct m ; repeat mysimp ; eauto
        ; remember (k <=>! k0') as m ; destruct m ; repeat mysimp ; eauto
        ; right ; repeat mysimp || rip || auto ; eauto.
    Qed.
    *)

    Lemma empty_tree_dp : forall t, empty_tree t \/ not_empty_tree t.
    Proof. intros t ; destruct t ; eauto. Qed.

    Ltac in_tree_case k t :=
      let Hin := fresh "Hin" in
      let Hmaps := fresh "Hmaps" in
      let Hnotin := fresh "Hnotin" in
      let v := fresh "v" in
      destruct (in_tree_dp k t) as [Hin | Hnotin]
      ; [apply in_to_maps in Hin ; destruct Hin as [v Hmaps]|].

    Lemma bst_tree_weaken :
      forall l_t l_t' u_t u_t' t,
      bst_tree l_t u_t t -> l_t' <= l_t -> u_t' >= u_t -> bst_tree l_t' u_t' t.
    Admitted.
    Hint Immediate bst_tree_weaken.

    (* Lemmas about fuse *)

    Lemma fuse_not_in :
      forall k c c',
      not_in_context k c
      -> not_in_context k c'
      -> not_in_context k (fuse c c').
    Admitted.
    Hint Resolve fuse_not_in.

    Lemma fuse_bst :
      forall l_m u_m l_t u_t c l_r u_r c',
      bst_context l_m u_m l_t u_t c
      -> bst_context l_r u_r l_m u_m c'
      -> bst_context l_r u_r l_t u_t (fuse c c').
    Admitted.
    Hint Resolve fuse_bst.

    Lemma fuse_balance :
      forall n n' c n'' c',
      balance_context n n' c
      -> balance_context n' n'' c'
      -> balance_context n n'' (fuse c c').
    Admitted.
    Hint Resolve fuse_balance.

    (* Lemmas about locate. *)

    Lemma locate_fail_eq :
      forall {k t} c, not_in_tree k t -> exists c', locate k t c = inl c'.
    Admitted.

    Lemma locate_success_eq :
      forall {k v t} c, maps_tree k v t -> exists l, locate k t c = inr (v,l).
    Admitted.

    Ltac locate_match_progress :=
      let Hex := fresh "Hex" in
      let c' := fresh "c'" in
      let l := fresh "l" in
      let Heq := fresh "Heq" in
      match goal with
      | [ |- context [ match locate ?k ?t ?c with _ => _ end ] ] =>
          match goal with
          | [ H : not_in_tree k t |- _ ] =>
              assert (exists c', locate k t c = inl c') as Hex
              ; [ eapply locate_fail_eq | destruct Hex as [c' Heq] ; rewrite Heq ]
          | [ H : maps_tree k ?v t |- _ ] =>
              assert (exists l, locate k t c = inr (v,l)) as Hex
              ; [ eapply locate_success_eq
                | destruct Hex as [l Heq] ; rewrite Heq
                ]
          | _ => in_tree_case k t ; locate_match_progress
          end
      | [ Hm : context [ match locate ?k ?t ?c with _ => _ end ] |- _ ] =>
          match goal with
          | [ H : not_in_tree k t |- _ ] =>
              assert (exists c', locate k t c = inl c') as Hex
              ; [ clear Hm ; eapply locate_fail_eq
                | destruct Hex as [c' Heq] ; rewrite Heq in Hm
                ]
          | [ H : maps_tree k ?v t |- _ ] =>
              assert (exists l, locate k t c = inr (v,l)) as Hex
              ; [ clear Hm ; eapply locate_success_eq
                | destruct Hex as [l Heq] ; rewrite Heq in Hm
                ]
          | _ => in_tree_case k t ; locate_match_progress
          end
      end.

    Lemma locate_fail_not_in :
      forall {k t c c'},
      locate k t c = inl c'
      -> not_in_tree k t
      -> not_in_context k c
      -> not_in_context k c'.
    Admitted.
    Hint Resolve locate_fail_not_in (* : forward_db *).

    Lemma locate_fail_in_tight1 :
      forall {k v k' t c c'},
      locate k' t c = inl c'
      -> maps_tree k v t \/ maps_context k v c
      -> maps_context k v c'.
    Admitted.
    Hint Resolve locate_fail_in_tight1 (* : forward_db *).

    Lemma locate_fail_in_tight2 :
      forall {k v k' t c c'},
      locate k' t c = inl c'
      -> maps_context k v c'
      -> not_in_context k c
      -> maps_tree k v t.
    Admitted.
    Hint Resolve locate_fail_in_tight2 (* : backward_db *).

    Lemma locate_fail_in_tight2' :
      forall {k v k' t c c'},
      locate k' t c = inl c'
      -> maps_context k v c'
      -> not_in_tree k t
      -> maps_context k v c.
    Admitted.
    Hint Resolve locate_fail_in_tight2' (* : backward_db *).

    Lemma locate_success_not_in :
      forall {k t c v l},
      locate k t c = inr (v,l)
      -> in_tree k t
      -> not_in_location k l.
    Admitted.
    Hint Resolve locate_success_not_in (* : forward_db *).

    Ltac pose_locate_success_not_in :=
      let Hnotin := fresh "Hnotin" in
      let n := fresh "n" in
      let finish Heq k l :=
        assert (not_in_location k l) as Hnotin
        ; [ eapply (locate_success_not_in Heq) ; clear Heq
          | inversion Hnotin ; subst ; clear Hnotin
          ]
      in
      match goal with
      | [ Heq : locate ?k ?t ?c = inr (_,TwoHole_l ?tl ?tr ?c') |- _ ] =>
          match goal with
          | [ Hbal : not_in_tree k tl |- _ ] => fail 1
          | _ => finish Heq k (TwoHole_l tl tr c')
          end
      | [ Heq : locate ?k ?t ?c = inr (_,ThreeLeftHole_l ?tl ?tm ?pr ?tr ?c') |- _ ] =>
          match goal with
          | [ Hbal : not_in_tree k tl |- _ ] => fail 1
          | _ => finish Heq k (ThreeLeftHole_l tl tm pr tr c')
          end
      | [ Heq : locate ?k ?t ?c = inr (_,ThreeRightHole_l ?tl ?pl ?tm ?tr ?c') |- _ ] =>
          match goal with
          | [ Hbal : not_in_tree k tl |- _ ] => fail 1
          | _ => finish Heq k (ThreeRightHole_l tl pl tm tr c')
          end
      end.

    Lemma locate_fail_bst_ex :
      forall {k l_t u_t t l_r u_r c c'},
      locate k t c = inl c'
      -> not_in_tree k t
      -> bst_tree l_t u_t t
      -> bst_context l_r u_r l_t u_t c
      -> exists l u, bst_context l_r u_r l u c' /\ l <= Extend k <= u.
    Admitted.
    Ltac locate_fail_bst_ex_tac :=
      match goal with
      | [ Heq : locate ?k ?t ?c = inl ?c'
        |- bst_tree ?l_t ?u_t (insert_up _ ?c')
        ] => match goal with
             | [ H : bst_context _ _ _ _ ?c' |- _ ] => fail
             | _ =>
               let Hex := fresh "Hex" in
               assert (exists l u, bst_context l_t u_t l u c' /\ l <= Extend k <= u) as Hex
               ; [ eapply locate_fail_bst_ex
                 | destruct Hex as [l Hex] ; destruct Hex as [u Hex] ; destruct Hex
                 ]
             end
      end.
    Hint Extern 1 => locate_fail_bst_ex_tac.

    Lemma locate_success_bst :
      forall {k l_t u_t t l_r u_r c v l},
      locate k t c = inr (v,l)
      -> in_tree k t
      -> bst_tree l_t u_t t
      -> bst_context l_r u_r l_t u_t c
      -> bst_location l_r u_r (Extend k) l.
    Admitted.
    Hint Resolve locate_success_bst (* : forward_db *).

    Lemma locate_fail_balance :
      forall {k n t n' c c'},
      locate k t c = inl c'
      -> not_in_tree k t
      -> balance_tree n t
      -> balance_context n n' c
      -> balance_context 0 n' c'.
    Admitted.
    Hint Resolve locate_fail_balance (* : forward_db *).

    Lemma locate_success_balance :
      forall {k n t n' c v l},
      locate k t c = inr (v,l)
      -> in_tree k t
      -> balance_tree n t
      -> balance_context n n' c
      -> balance_location n' l.
    Admitted.
    Hint Resolve locate_success_balance (* : forward_db *).

    Ltac pose_locate_success_balance :=
      let Hex := fresh "Hex" in
      let Hbal := fresh "Hbal" in
      let n := fresh "n" in
      let finish Heq l :=
        assert (exists n, balance_location n l) as Hex
        ; [ econstructor ; eapply (locate_success_balance Heq) ; clear Heq
          | destruct Hex as [n Hbal] ; inversion Hbal ; subst ; clear Hbal
          ]
      in
      match goal with
      | [ Heq : locate ?k ?t ?c = inr (_,TwoHole_l ?tl ?tr ?c') |- _ ] =>
          match goal with
          | [ Hbal : balance_tree _ tl |- _ ] => fail 1
          | _ => finish Heq (TwoHole_l tl tr c')
          end
      | [ Heq : locate ?k ?t ?c = inr (_,ThreeLeftHole_l ?tl ?tm ?pr ?tr ?c') |- _ ] =>
          match goal with
          | [ Hbal : balance_tree _ tl |- _ ] => fail 1
          | _ => finish Heq (ThreeLeftHole_l tl tm pr tr c')
          end
      | [ Heq : locate ?k ?t ?c = inr (_,ThreeRightHole_l ?tl ?pl ?tm ?tr ?c') |- _ ] =>
          match goal with
          | [ Hbal : balance_tree _ tl |- _ ] => fail 1
          | _ => finish Heq (ThreeRightHole_l tl pl tm tr c')
          end
      end.

    (* Lemmas about lookup. *)

    Lemma lookup_success_eq : forall {k v t}, maps_tree k v t -> lookup k t = Some v.
    Proof. intros k v t Ht ; unfold lookup ; locate_match_progress ; eauto. Qed.

    Program Definition lookup_total k t (Ht:in_tree k t) : V :=
      match lookup k t with
      | None => False_rect _ _
      | Some v => v
      end.
    Next Obligation.
      destruct (in_to_maps Ht) as [v Hmaps] ; rewrite (lookup_success_eq Hmaps) in * ; congruence.
    Qed.

    (* Lemmas about fill_location *)

    Lemma fill_location_maps :
      forall {k v l},
      not_in_location k l -> maps_tree k v (fill_location (k,v) l).
    Admitted.
    Hint Resolve fill_location_maps (* : forward_db *).

    Lemma fill_location_maps_tight1 :
      forall {k k' v v' v'' t c l},
      locate k' t c = inr (v',l)
      -> k /~= k'
      -> maps_tree k v t \/ maps_context k v c
      -> maps_tree k v (fill_location (k',v'') l).
    Admitted.
    Hint Resolve fill_location_maps_tight1 (* : forward_db *).

    Lemma fill_location_maps_tight2 :
      forall k k' v v' v'' t c l,
      locate k' t c = inr (v',l)
      -> k /~= k'
      -> maps_tree k v (fill_location (k',v'') l)
      -> not_in_context k c
      -> maps_tree k v t.
    Admitted.
    Hint Resolve fill_location_maps_tight2 (* : backward_db *).

    Lemma fill_location_maps_tight2' :
      forall k k' v v' v'' t c l,
      locate k' t c = inr (v',l)
      -> k /~= k'
      -> maps_tree k v (fill_location (k',v'') l)
      -> not_in_tree k t
      -> maps_context k v c.
    Admitted.
    Hint Resolve fill_location_maps_tight2' (* : backward_db *).

    Lemma fill_location_bst :
      forall k v l_r u_r l,
      bst_location l_r u_r (Extend k) l
      -> bst_tree l_r u_r (fill_location (k,v) l).
    Admitted.
    Hint Resolve fill_location_bst (* : forward_db *).

    Lemma fill_location_balance :
      forall k v n l ,
      balance_location n l
      -> balance_tree n (fill_location (k,v) l).
    Admitted.
    Hint Resolve fill_location_balance (* : forward_db *).

    (* Lemmas about locate_greatest *)

    Lemma locate_greatest_fail_eq : forall {t c}, empty_tree t -> locate_greatest t c = None.
    Admitted.

    Lemma locate_greatest_success_eq :
      forall {t c}, not_empty_tree t -> exists k v lM, locate_greatest t c = Some ((k,v),lM).
    Admitted.

    Ltac locate_greatest_match_progress :=
      let Hex := fresh "Hex" in
      let k := fresh "k'" in
      let v := fresh "v'" in
      let lM := fresh "lM'" in
      let Heq := fresh "Heq" in
      match goal with
      | [ |- context [ match locate_greatest ?t ?c with _ => _ end ] ] =>
          match goal with
          | [ H : empty_tree t |- _ ] =>
              assert (locate_greatest t c = None) as Heq
              ; [ eapply locate_greatest_fail_eq | rewrite Heq ]
          | [ H : not_empty_tree t |- _ ] =>
              assert (exists k v lM, locate_greatest t c = Some ((k,v),lM)) as Hex
              ; [ eapply locate_greatest_success_eq
                | destruct Hex as [k Hex] ; destruct Hex as [v Hex]
                  ; destruct Hex as [lM Heq] ; rewrite Heq ]
          | _ => destruct (empty_tree_dp t) ; locate_greatest_match_progress
          end
      | [ Hm : context [ match locate_greatest ?t ?c with _ => _ end ] |- _ ] =>
          match goal with
          | [ H : empty_tree t |- _ ] =>
              assert (locate_greatest t c = None) as Heq
              ; [ clear Hm ; eapply locate_greatest_fail_eq | rewrite Heq in Hm ]
          | [ H : not_empty_tree t |- _ ] =>
              assert (exists k v lM, locate_greatest t c = Some ((k,v),lM)) as Hex
              ; [ clear Hm ; eapply locate_greatest_success_eq
                | destruct Hex as [k Hex] ; destruct Hex as [v Hex]
                  ; destruct Hex as [lM Heq] ; rewrite Heq in Hm ]
          | _ => destruct (empty_tree_dp t) ; locate_greatest_match_progress
          end
      end.

    Lemma locate_greatest_success_two_not_in :
      forall {k k' v' t c c'},
      locate_greatest t c = Some ((k',v'), inl c')
      -> not_in_tree k t
      -> not_in_context k c
      -> not_in_context k c'.
    Admitted.
    Hint Resolve locate_greatest_success_two_not_in.

    Lemma locate_greatest_success_two_result_ineq :
      forall {k k' v t c c'},
      locate_greatest t c = Some (k', v, inl c')
      -> not_in_tree k t
      -> k /~= k'.
    Admitted.
    Hint Resolve locate_greatest_success_two_result_ineq.

    Lemma locate_greatest_success_two_bst :
      forall {k v l_t u_t t l_r u_r c c'},
      locate_greatest t c = Some ((k,v), inl c')
      -> bst_tree l_t u_t t
      -> bst_context l_r u_r l_t u_t c
      -> exists l_p u_p, bst_context l_r (Extend k) l_p u_p c' /\ Extend k <= u_t.
    Admitted.

    Lemma locate_greatest_success_two_balance :
      forall {n t n' c k v c'},
      locate_greatest t c = Some ((k,v),inl c')
      -> balance_tree n t
      -> balance_context n n' c
      -> balance_context (0+1) n' c'.
    Admitted.
    Hint Resolve locate_greatest_success_two_balance (* : forward_db *).

    (* Lemmas about insert_up *)

    Lemma insert_up_maps :
      forall {k v tl tr c},
      not_in_context k c -> maps_tree k v (insert_up (tl,(k,v),tr) c).
    Admitted.
    Hint Resolve insert_up_maps (* : forward_db *).

    Lemma insert_up_tight1 :
      forall {k k' v v' tl tr c},
      k /~= k'
      -> maps_context k v c
      -> maps_tree k v (insert_up (tl,(k',v'),tr) c).
    Admitted.
    Hint Resolve insert_up_tight1 (* : forward_db *).

    Lemma insert_up_tight2 :
      forall {k k' v v' tl tr c},
      k /~= k'
      -> maps_tree k v (insert_up (tl,(k',v'),tr) c)
      -> maps_context k v c.
    Admitted.
    Hint Resolve insert_up_tight2 (* : backward_db *).

    Lemma insert_up_bst :
      forall {k v u_tl tl l_tr tr l_r u_r l_t u_t c},
      bst_context l_r u_r l_t u_t c
      -> bst_tree l_t u_tl tl
      -> u_tl <= Extend k <= l_tr
      -> bst_tree l_tr u_t tr
      -> bst_tree l_r u_r (insert_up (tl,(k,v),tr) c).
    Admitted.
    Hint Resolve insert_up_bst (* : forward_db *).

    Lemma insert_up_balance :
      forall n tl k v tr n' c,
      balance_tree n tl
      -> balance_tree n tr
      -> balance_context n n' c
      -> exists n'', balance_tree n'' (insert_up (tl,(k,v),tr) c).
    Admitted.
    Hint Resolve insert_up_balance.

    (* Lemmas about insert_with. *)

    Lemma insert_with_not_in :
      forall {f k v t}, not_in_tree k t -> maps_tree k v (insert_with f k v t).
    Proof. intros ; unfold insert_with ; locate_match_progress ; eauto 3. Qed.

    Lemma insert_with_in :
      forall {f k v v' t}, maps_tree k v' t -> maps_tree k (f v v') (insert_with f k v t).
    Proof. intros ; unfold insert_with ; locate_match_progress ; eauto 4. Qed.

    Lemma insert_with_in_tight1 :
      forall {f k k' v v' t},
      k /~= k' -> maps_tree k v t -> maps_tree k v (insert_with f k' v' t).
    Proof. intros ; unfold insert_with ; in_tree_case k' t ; locate_match_progress ; eauto. Qed.

    Lemma insert_with_in_tight2 :
      forall {f k k' v v' t},
      k /~= k' -> maps_tree k v (insert_with f k' v' t) -> maps_tree k v t.
    Proof. intros ; unfold insert_with in * ; in_tree_case k' t ; locate_match_progress ; eauto. Qed.

    Lemma insert_with_bst :
      forall {f k v l_t u_t t},
      l_t <= Extend k <= u_t -> bst_tree l_t u_t t -> bst_tree l_t u_t (insert_with f k v t).
    Proof. intros ; unfold insert_with in * ; in_tree_case k' t ; locate_match_progress ; eauto. Qed.

    Lemma insert_with_balance :
      forall f k v n t,
      balance_tree n t -> exists n', balance_tree n' (insert_with f k v t).
    Proof. intros ; unfold insert_with in * ; in_tree_case k t ; locate_match_progress ; eauto. Qed.

    (* Lemmas about remove_up *)

    Lemma remove_up_wf :
      forall {n t n' c},
      balance_tree n t -> balance_context (n+1) n' c -> exists t', remove_up t c = Some t'.
    Admitted.
    (*
    Proof.
      intros n t n' c ; gd n' ; gd t ; gd n ; induction c ; intros ; simpl
      ; repeat mysimp || rip || atom_match_drill || auto ; eauto.
    Qed.
    *)

    Lemma remove_up_not_in :
      forall {k t c t'},
      remove_up t c = Some t'
      -> not_in_tree k t
      -> not_in_context k c
      -> not_in_tree k t'.
    Admitted.
    Hint Resolve remove_up_not_in.

    Ltac remove_up_wf_progress_goal :=
      let Heq := fresh "Heq" in
      let t' := fresh "t'" in
      match goal with
      | [ |- context [ remove_up ?t ?c ] ] =>
          assert (exists t', remove_up t c = Some t') as Hex
          ; [ eapply remove_up_wf
            | destruct Hex as [t' Heq] ; rewrite Heq
            ]
      end.

    (* Lemmas about remove *)

    Lemma remove_wf :
      forall k v n t,
      balance_tree n t -> maps_tree k v t -> exists t', remove k t = Some (t',Some v).
    Proof.
      intros ; unfold remove
      ; repeat
          mysimp || locate_match_progress || locate_greatest_match_progress
          || let_pair_drill || atom_match_drill
          || pose_locate_success_balance
          || remove_up_wf_progress_goal
      ; eauto ; try (compute ; eauto ; fail).
    Qed.

    Ltac fmap_success_eq :=
      match goal with
      | [ H : fmap ?f ?xM = Some ?x |- _ ] =>
          let X := fresh "X" in
          remember xM as X ; flip_eqn xM ; destruct X ; unfold fmap in * ; simpl in *
          ; try congruence ;
          match goal with [ H : Some _ = Some _ |- _ ] => injection H ; intros ; subst ; clear H end
      end.
          

    Lemma remove_in :
      forall k t t' vM,
      remove k t = Some (t',vM) -> not_in_tree k t'.
    Proof.
      intros ; unfold remove in *
      ; repeat
          mysimp
          || locate_match_progress
          || locate_greatest_match_progress
          || let_pair_drill || atom_match_drill
          || pose_locate_success_not_in
          || fmap_success_eq
      ; eauto.
      locate_greatest_match_progress.
      eapply remove_up_not_in ; eauto.
      eapply fuse_not_in ; eauto.
      destruct p.
      eauto.
      eauto.
      eapply locate_greatest_success_two_not_in ; eauto.
      
      ea
      fmap_success_eq.
      - remember (remove_up Null_t c) as X eqn:eqn ; symmetry in eqn
        ; destruct X ; unfold fmap in * ; simpl in * ; try congruence
        ; injection H ; intros ; subst ; clear H ; eauto.
      - 
        eauto.
      assert (not_in_context k c).
      { eauto.
        Lemma
          locate k t c = inr (v,l)
          -> 
      eauto.
      admit.
      unfold fmap in H ; simpl in H.
      soimp
      Lemma
        f <$> x = Some y -> x = Some (f y)kk
      simpl in H.
      remove_up_
      ; repeat let_pair_drill || locate_drill || locate_greatest_drill || match_drill.
      admit.
      simpl in *.

        inversion H5 ; subst ; clear H5.
        match goal with
                     

        subst.

      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
    Qed.


    (* ############ *)

    Definition in_two_node_lib :
      forall tl km vm tr, in_tree km (Two_t tl (km,vm) tr).
    Proof. intros ; apply In_TwoNode ; reflexivity. Qed.
    Hint Resolve in_two_node_lib.

    Definition in_three_left_node_lib :
      forall tl kl vl tm pr tr, in_tree kl (Three_t tl (kl,vl) tm pr tr).
    Proof. intros ; apply In_ThreeLeftNode ; reflexivity. Qed.
    Hint Resolve in_three_left_node_lib.

    Definition in_three_right_node_lib :
      forall tl pl tm kr vr tr, in_tree kr (Three_t tl pl tm (kr,vr) tr).
    Proof. intros ; apply In_ThreeRightNode ; reflexivity. Qed.
    Hint Resolve in_three_right_node_lib.

    Lemma bst_tree_order : forall l u t, bst_tree l u t -> l <= u.
    Proof.
      intros l u t bstt ; gd u ; gd l ; induction t ; intros ; repeat mysimp || rip || auto ; eauto.
      - transitivity (Extend k) ; eauto.
      - transitivity (Extend kl) ; [|transitivity (Extend kr)] ; eauto.
    Qed.
    Hint Immediate bst_tree_order.

    Lemma extend_bst_eqv_l :
      forall {k k' l t1}, bst_tree l (Extend k) t1 -> k' ~= k -> l <= Extend k'.
    Proof.
      intros.
      refine (PartialOrd_respect_eqv l l _ (Extend k) (Extend k') _ _)
      ; eauto ; [reflexivity | symmetry].
      apply InjectionRespect_eta ; auto.
    Qed.
    Hint Extern 0 =>
      match goal with
      | [ H1 : bst_tree ?l (Extend ?k) _
        , H2 : ?k' ~= ?k
        |- ?l <= Extend ?k'
        ] => apply (extend_bst_eqv_l H1 H2)
      end.

    Lemma extend_bst_eqv_l2 :
      forall {k k' l m t1 t2},
      bst_tree l m t1 -> bst_tree m (Extend k) t2 -> k' ~= k -> l <= Extend k'.
    Proof. intros ; transitivity m ; eauto. Qed.
    Hint Extern 0 =>
      match goal with
      | [ H1 : bst_tree ?l ?m _
        , H2 : bst_tree ?m (Extend ?k) _
        , H3 : ?k' ~= ?k
        |- ?l <= Extend ?k'
        ] => apply (extend_bst_eqv_l2 H1 H2 H3)
      end.

    Lemma extend_bst_eqv_u :
      forall {k k' u t1}, bst_tree (Extend k) u t1 -> k' ~= k -> Extend k' <= u.
    Proof.
      intros.
      refine (PartialOrd_respect_eqv (Extend k) (Extend k') _ u u _ _)
      ; eauto ; [symmetry | reflexivity].
      apply InjectionRespect_eta ; auto.
    Qed.
    Hint Extern 0 =>
      match goal with
      | [ H1 : bst_tree (Extend ?k) ?u _
        , H2 : ?k' ~= ?k
        |- Extend ?k' <= ?u
        ] => apply (extend_bst_eqv_u H1 H2)
      end.

    Lemma extend_bst_eqv_u2 :
      forall {k k' m u t1 t2},
      bst_tree (Extend k) m t1 -> bst_tree m u t2 -> k' ~= k -> Extend k' <= u.
    Proof. intros ; transitivity m ; eauto. Qed.
    Hint Extern 0 =>
      match goal with
      | [ H1 : bst_tree (Extend ?k) ?m _
        , H2 : bst_tree ?m ?u _
        , H3 : ?k' ~= ?k
        |- Extend ?k' <= ?u
        ] => apply (extend_bst_eqv_u2 H1 H2 H3)
      end.

    Lemma extend_bst_lte_l : forall l m u t1, l <= m -> bst_tree m u t1 -> l <= u.
    Proof. intros ; transitivity m ; eauto. Qed.
    Hint Immediate extend_bst_lte_l.

    Lemma extend_bst_lte_l2
      : forall l ml mr u t1 t2, l <= ml -> bst_tree ml mr t1 -> bst_tree mr u t2 -> l <= u.
    Proof. intros ; transitivity mr ; eauto. Qed.
    Hint Immediate extend_bst_lte_l2.

    Lemma extend_bst_lte_u : forall l m u t1 , bst_tree l m t1 -> m <= u -> l <= u.
    Proof. intros ; transitivity m ; eauto. Qed.
    Hint Immediate extend_bst_lte_u.

    Lemma extend_bst_lte_u2 :
      forall l ml mr u t1 t2, bst_tree l ml t1 -> bst_tree ml mr t2 -> mr <= u -> l <= u.
    Proof. intros ; transitivity ml ; eauto. Qed.
    Hint Immediate extend_bst_lte_u2.

    Lemma bst_tree_order_trans : forall l m u t1 t2, bst_tree l m t1 -> bst_tree m u t2 -> l <= u.
    Proof.
      intros ; transitivity m ; eauto.
    Qed.
    Hint Immediate bst_tree_order_trans.

    Lemma in_bst_tree_order : forall {k l u t}, bst_tree l u t -> in_tree k t -> l <= Extend k <= u.
    Proof.
      intros k l u t bstt int ; gd u ; gd l ; induction t ; intros
      ; repeat mysimp ||
        match goal with
        | [ IH : in_tree _ ?t -> forall l u, bst_tree l u ?t -> _
          , Hin : in_tree _ ?t
          , HB : bst_tree ?l ?u ?t |- _
          ] => specialize (IH Hin l u HB)
        end || rip || auto ; eauto.
    Qed.
    Hint Immediate in_bst_tree_order.

    Lemma in_bst_tree_order_l : forall {k l u t}, bst_tree l u t -> in_tree k t -> l <= Extend k.
    Proof. intros k l u t H1 H2 ; apply (in_bst_tree_order H1 H2). Qed.
    Hint Immediate in_bst_tree_order_l.

    Lemma in_bst_tree_order_l' :
      forall {kl km u t}, bst_tree (Extend kl) u t -> in_tree km t -> kl <= km.
    Proof. intros ; apply InjectionRespect_beta ; eauto. Qed.
    Hint Immediate in_bst_tree_order_l'.

    Lemma in_bst_tree_order_u : forall {k l u t}, bst_tree l u t -> in_tree k t -> Extend k <= u.
    Proof. intros k l u t H1 H2 ; apply (in_bst_tree_order H1 H2). Qed.
    Hint Immediate in_bst_tree_order_u.

    Lemma in_bst_tree_order_u' :
      forall {l km ku t}, bst_tree l (Extend ku) t -> in_tree km t -> km <= ku.
    Proof. intros ; apply InjectionRespect_beta ; eauto. Qed.
    Hint Immediate in_bst_tree_order_u'.

    Lemma in_tree_lt_contradiction :
      forall {k k' u t}, bst_tree (Extend k') u t -> in_tree k t -> k < k' -> False.
    Proof. intros k k' u t Hbst Hin Hlt ; apply Hlt ; eauto. Qed.
    Hint Extern 0 =>
      match goal with
      | [ H1 : bst_tree (Extend ?k') ?u ?t , H2 : in_tree ?k ?t , H3 : ?k < ?k' |- _ ] =>
          exfalso ; apply (in_tree_lt_contradiction H1 H2 H3)
      end.

    Lemma in_Two_t_lt_pm_refine :
      forall k l_tl tl km vm u_tr tr,
      bst_tree l_tl u_tr (Two_t tl (km,vm) tr)
      -> in_tree k (Two_t tl (km,vm) tr)
      -> k < km
      -> in_tree k tl.
    Proof.
      intros ; repeat mysimp || rip || auto ; eauto.
    Qed.
    Hint Resolve in_Two_t_lt_pm_refine.
      
    Lemma zip_in_t : forall k t c, in_tree k t -> in_tree k (zip t c).
    Proof. intros k t c ; gd t ; induction c ; intros ; simpl ; auto. Qed.
    Hint Resolve zip_in_t.

    Lemma zip_in_c : forall k t c, in_context k c -> in_tree k (zip t c).
    Proof.
      intros k t c ; gd t ; induction c ; intros ; simpl ; repeat mysimp || rip || auto ; eauto.
    Qed.
    Hint Resolve zip_in_c.

    Lemma zip_bst :
      forall l_r u_r l_h u_h t c,
      bst_tree l_h u_h t
      -> bst_context l_r u_r l_h u_h c
      -> bst_tree l_r u_r (zip t c).
    Proof.
      intros l_r u_r l_h u_h t c bstt bstc ; gd t ; gd u_h ; gd l_h ; induction c ; intros ; simpl
      ; mysimp ; eauto.
    Qed.
    Hint Resolve zip_bst.

    Lemma zip_height :
      forall n n' t c, height_tree n t -> height_context n n' c -> height_tree n' (zip t c).
    Proof. intros n n' t c ; gd t ; gd n ; induction c ; intros ; simpl ; mysimp ; eauto. Qed.
    Hint Resolve zip_height.

    Lemma fuse_in_c1 : forall k c1 c2, in_context k c1 -> in_context k (fuse c1 c2).
    Proof.
      intros k c1 c2 inc1 ; induction c1 ; intros ; simpl ; repeat mysimp || rip || auto ; eauto.
    Qed.
    Hint Resolve fuse_in_c1.

    Lemma fuse_in_c2 : forall k c1 c2, in_context k c2 -> in_context k (fuse c1 c2).
    Proof. intros k c1 c2 inc1 ; induction c1 ; intros ; simpl ; auto. Qed.
    Hint Resolve fuse_in_c2.
      
    Lemma fuse_bst :
      forall l_r u_r l_h u_h c1 l_r' u_r' c2,
      bst_context l_r u_r l_h u_h c1
      -> bst_context l_r' u_r' l_r u_r c2
      -> bst_context l_r' u_r' l_h u_h (fuse c1 c2).
    Proof.
      intros l_r u_r l_h u_h c1 l_r' u_r' c2 bstc1 bstc2
      ; gd u_h ; gd l_h ; induction c1 ; intros ; simpl
      ; mysimp ; eauto.
    Qed.
    Hint Resolve fuse_bst.

    Lemma fuse_height :
      forall n n' c1 n'' c2,
      height_context n n' c1
      -> height_context n' n'' c2
      -> height_context n n'' (fuse c1 c2).
    Proof.
      intros n n' c1 n'' c2 heightc1 heightc2
      ; gd n ; induction c1 ; intros ; simpl ; mysimp ; auto.
    Qed.
    Hint Resolve fuse_height.

    Lemma fill_location_in_k : forall k v l, in_tree k (fill_location (k,v) l).
    Proof. intros k v l ; destruct l ; simpl ; auto. Qed.
    Hint Resolve fill_location_in_k.

    Lemma fill_location_in_l : forall k v l, in_location k l -> in_tree k (fill_location (k,v) l).
    Proof. intros k v l inloc ; destruct l ; simpl ; auto. Qed.
    Hint Resolve fill_location_in_l.
      
    Lemma fill_location_bst :
      forall k v l_r u_r l,
      bst_location l_r u_r (Extend k) l
      -> bst_tree l_r u_r (fill_location (k,v) l).
    Proof. intros k v l_r u_r l bstloc ; destruct l ; simpl ; mysimp ; eauto. Qed.
    Hint Resolve fill_location_bst.

    Lemma fill_location_height :
      forall k v n l, height_location n l -> height_tree n (fill_location (k,v) l).
    Proof. intros k v n l heightl ; gd n ; destruct l ; intros ; simpl ; mysimp ; eauto. Qed.
    Hint Resolve fill_location_height.

    Ltac locate_drill :=
      match goal with
      | [ |- context [ let (_,_) := ?p in _ ] ] => destruct p
      | [ |- context [ ?x <=>! ?y ] ] => remember (x <=>! y) as m ; destruct m
      | [ H : Lt = _ |- _ ] => symmetry in H ; apply tord_dec_correct_lt in H
      | [ H : Eq = _ |- _ ] => symmetry in H ; apply tord_dec_correct_eqv in H
      | [ H : Gt = _ |- _ ] => symmetry in H ; apply tord_dec_correct_gt in H
      | [ IH : forall c, match locate ?k ?t c with _ => _ end
        |- match locate ?k ?t ?c with _ => _ end
        ] => specialize (IH c) ; remember (locate k t c) as m ; destruct m ; intros
      | [ IH : forall c, _ -> match locate ?k ?t c with _ => _ end
        |- match locate ?k ?t ?c with _ => _ end
        ] => specialize (IH c) ; remember (locate k t c) as m ; destruct m ; intros
        | [ IH : forall l_t u_t, _ -> forall c, match locate ?k ?t c with _ => _ end
          , H : bst_tree ?l_t ?u_t ?t
          |- match locate ?k ?t ?c with _ => _ end
          ] => specialize (IH l_t u_t H c) ; remember (locate k t c) as m ; destruct m ; intros
      end.

    Lemma locate_in_fail_in_t_c :
      forall k {l_t u_t t} c,
      bst_tree l_t u_t t
      -> match locate k t c with
         | inl c' => forall k', in_tree k' t \/ in_context k' c -> in_context k' c'
         | inr _ => True
         end.
    Proof.
      intros k l_t u_t t c bstt ; gd c ; gd u_t ; gd l_t ; induction t ; simpl ; intros
      ; repeat mysimp || locate_drill || rip || auto ; eauto.
    Qed.

    Lemma locate_in_fail_in_t :
      forall k l_t u_t t c,
      bst_tree l_t u_t t
      -> match locate k t c with
         | inl c' => forall k', in_tree k' t -> in_context k' c'
         | inr _ => True
         end.
    Proof.
      intros k l_t u_t t c Hbst ; remember (locate_in_fail_in_t_c k c Hbst) eqn:eqn ; clear eqn
      ; destruct (locate k t c) ; eauto.
    Qed.

    Lemma locate_in_fail_in_c :
      forall k l_t u_t t c,
      bst_tree l_t u_t t
      -> match locate k t c with
         | inl c' => forall k', in_context k' c -> in_context k' c'
         | inr _ => True
         end.
    Proof.
      intros k l_t u_t t c Hbst ; remember (locate_in_fail_in_t_c k c Hbst) eqn:eqn ; clear eqn
      ; destruct (locate k t c) ; eauto.
    Qed.

    Lemma locate_in_success_k :
      forall k (t:tree K V) c,
      match locate k t c with
      | inl _ => True
      | inr ((k',_),_) => in_tree k t /\ k ~= k'
      end.
    Proof.
      intros k t c ; gd c ; induction t ; intros ; simpl
      ; repeat mysimp || locate_drill ||
        match goal with
        end || rip || auto ; eauto.               
    Qed.

  Lemma remove_in :
    forall t k t_lower t_upper t_height,
    tree_iwf t_lower t_upper t_height t
    -> match remove k t with
       | None => True
       | Some (t',_) =>
         forall k', k' /~= k -> in_tree k' t -> in_tree k' t'
       end.
  Proof.
    intros t ; induction t ; simpl ; intros ; auto.
    - unfold remove ; simpl.
      destruct p.
      remember (k <=>! k0) as m eqn:meqn
      ; symmetry in meqn ; destruct m
      ; [ apply tord_dec_correct_eqv in meqn
        | apply tord_dec_correct_lt in meqn
        | apply tord_dec_correct_gt in meqn
        ].
      + remember (locate_greatest t1 Top_c) as m ; destruct m ; simpl.
        { destruct p.
          destruct s.
          - destruct t2 ; simpl ; auto.
            + remember (remove_up (Three_t Null_t p t2_1 p0 t2_2) (fuse c Top_c)) as m ; destruct m ; simpl ; intros.
              { pose (remove_up_in_tree (fuse c Top_c) (Three_t Null_t p t2_1 p0 t2_2)).
                rewrite <- Heqm0 in y.
                apply y.
                pose (locate_greatest_in t1 Top_c).
                rewrite <- Heqm in y0 ; destruct p ; simpl in y0.
                pose (locate_greatest_in_result t1 Top_c).
                rewrite <- Heqm in y1.
                specialize (y0 k).
                inversion H1 ; subst ; clear H1.
                - specialize (y0 k).
    
  Lemma remove_spec :
    forall k t t_lower t_upper t_height,
    tree_iwf t_lower t_upper t_height t
    -> match remove k t with
       | None => True
       | Some (t',vM) =>
           ~ in_tree k t'
           /\ (forall k', k' /~= k -> in_tree k' t -> in_tree k' t')
           /\ match vM with
              | None => ~ in_tree k t
              | Some v => in_tree k t /\ lookup k t = Some v
              end
           /\
       end.
            
      
           
  Program Definition empty_wf : with_wf (tree K V) := exist _ empty _.
  Next Obligation.
    exists 0, (lbot:extend K) , (lbot:extend K) ; constructor ; reflexivity.
  Defined.

  Program Definition singleton_wf (k:K) (v:V) : with_wf (tree K V) := exist _ (singleton k v) _.
  Next Obligation.
    exists (0+1), (lbot:extend K), (ltop:extend K).
    econstructor ; eauto ; constructor ; [ apply lbot_ineq | apply ltop_ineq ].
  Defined.

  Definition tree_inwf (k:K) (twf:with_wf (tree K V)) : Prop := in_tree k (proj1_sig twf).

  Definition lookup_wf (k:K) (twf:with_wf (tree K V)) `(! tree_inwf k twf ) : V.
  Proof.
    destruct twf as [t p].
    elimtype { v | lookup k t = Some v} ; intros.
    { exact x. }
    unfold lookup ; unfold tree_inwf in tree_inwf0 ; simpl in tree_inwf0
    ; remember (locate k t Top_c) as m ; destruct m
    ; pose (locate_in t k Top_c) ; rewrite <- Heqm in y ; repeat mysimp.
    - exfalso.
      destruct p as [n Ex] ; destruct Ex as [kM Ex] ; destruct Ex.
      pose (locate_not_in k Top_c H).
      rewrite <- Heqm in y0.
      contradiction.
    - econstructor ; reflexivity.
  Qed.

  
  
End TwoThreeTreesWF.

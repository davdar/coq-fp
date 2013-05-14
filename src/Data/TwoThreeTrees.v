Require Import FP.CoreData.
Require Import FP.CoreClasses.
Require Import FP.Categories.
Require Import FP.Data.Option.
Require Import FP.Data.List.
Require Import FP.Data.Foldable.
Require Import FP.Data.Monoid.
Require Import FP.Data.Prod.

Import CoreDataNotation.
Import CoreClassesNotation.
Import CategoriesNotation.

Module TwoThreeTrees.
  Section Context.
    Context {K:Type} `{! TotalOrdDec K }.
    Context {V:Type}.

    (* a two-three tree *)
    Inductive tree :=
      (* Null_t = _ *)
      | Null_t : tree
      (*                [a]
       * Two_t X a Y =  / \
       *               X   Y
       * Invariant: x in X => x < a; y in Y => y > a
       *)
      | Two_t : tree -> K*V -> tree -> tree
      (*                       [a][b]
       * Three_t X a Y b Z =  /  |  \
       *                     X   Y   Z
       * Invariant: x in X => x < a; y in Y => a < y < b; z in Z => z > b
       *)
      | Three_t : tree -> K*V -> tree -> K*V -> tree -> tree.

    Definition empty := Null_t.
    Definition single (e:K*V) : tree := Two_t Null_t e Null_t.
    Definition singleton (k:K) (v:V) : tree := Two_t Null_t (k,v) Null_t.

    (* a context of a two-three tree. this is the type of taking a tree and
     * replacing a sub-tree with a hole.
     *)
    Inductive context :=
      (* Top_c = _ *)
      | Top_c : context
      (*                         C
       * TwoLeftHole_c a Y C =   |
       *                        [a]
       *                        / \
       *                       ?   Y
       *)
      | TwoLeftHole_c : K*V -> tree -> context -> context
      (*                          C
       * TwoRightHole_c X a C =   |
       *                         [a]
       *                         / \
       *                        X   ?
       *)
      | TwoRightHole_c : tree -> K*V -> context -> context
      (*                             C
       * ThreeLeftHole a Y b Z C =   |
       *                           [a][b]
       *                          /  |  \
       *                         ?   Y   Z
       *)
      | ThreeLeftHole_c : K*V -> tree -> K*V -> tree -> context -> context 
      (*                               C
       * ThreeMiddleHole X a b Z C =   |
       *                             [a][b]
       *                            /  |  \
       *                           X   ?   Z
       *)
      | ThreeMiddleHole_c : tree -> K*V -> K*V -> tree -> context -> context
      (*                                C
       * ThreeRightHole_c X a Y b C =   |
       *                              [a][b]
       *                             /  |  \
       *                            X   Y   ?
       *)
      | ThreeRightHole_c : tree -> K*V -> tree -> K*V -> context -> context.

    (* zip takes a context (which can be thought of as a tree with a hole), and a
     * subtree, and fills the hole with the subtree
     *)
    Fixpoint zip (t:tree) (c:context) : tree :=
      match c with
      | Top_c => t
      | TwoLeftHole_c em tr c' => zip (Two_t t em tr) c'
      | TwoRightHole_c tl em c' => zip (Two_t tl em t) c'
      | ThreeLeftHole_c el em er tr c' => zip (Three_t t el em er tr) c'
      | ThreeMiddleHole_c tl el er tr c' => zip (Three_t tl el t er tr) c'
      | ThreeRightHole_c tl el em er c' => zip (Three_t tl el em er t) c'
      end.

    Fixpoint fuse (c1:context) (c2:context) : context :=
      match c1 with
      | Top_c => c2
      | TwoLeftHole_c em tr c1' => TwoLeftHole_c em tr $ fuse c1' c2
      | TwoRightHole_c tl em c1' => TwoRightHole_c tl em $ fuse c1' c2
      | ThreeLeftHole_c el em er tr c1' => ThreeLeftHole_c el em er tr $ fuse c1' c2
      | ThreeMiddleHole_c tl el er tr c1' => ThreeMiddleHole_c tl el er tr $ fuse c1' c2
      | ThreeRightHole_c tl el em er c1' => ThreeRightHole_c tl el em er $ fuse c1' c2
      end.

    Inductive location :=
      (*                     C
       * TwoHole_l X Y C =   |
       *                    [?]
       *                    / \
       *                   X   Y
       *)
      | TwoHole_l : tree -> tree -> context -> location
      (*                         C
       * TwoHole_l X Y b Z C =   |
       *                       [?][b]
       *                       /  |  \
       *                      X   Y   Z
       *)
      | ThreeLeftHole_l : tree -> tree -> K*V -> tree -> context -> location
      (*                         C
       * TwoHole_l X a Y Z C =   |
       *                       [a][?]
       *                       /  |  \
       *                      X   Y   Z
       *)
      | ThreeRightHole_l : tree -> K*V -> tree -> tree -> context -> location.

    Definition fill_location (e:K*V) (l:location) : tree :=
      match l with
      | TwoHole_l tl tr c => zip (Two_t tl e tr) c
      | ThreeLeftHole_l tl tm vr tr c => zip (Three_t tl e tm vr tr) c
      | ThreeRightHole_l tl el tm tr c => zip (Three_t tl el tm e tr) c
      end.

    (* returns either a context where the key would be located or an
       existing pair and its location *)
    Fixpoint locate (k:K) (t:tree) (c:context) : context + (K*V) * location :=
      match t with
      | Null_t => inl c
      | Two_t tl (km,vm) tr =>
          match k <=>! km with
          | Lt => locate k tl $ TwoLeftHole_c (km,vm) tr c
          | Eq => inr ((km,vm), TwoHole_l tl tr c)
          | Gt => locate k tr $ TwoRightHole_c tl (km,vm) c
          end
      | Three_t tl (kl,vl) tm (kr,vr) tr =>
          match k <=>! kl, k <=>! kr with
          | Lt, _ => locate k tl $ ThreeLeftHole_c (kl,vl) tm (kr,vr) tr c
          | Eq, _ => inr ((kl,vl), ThreeLeftHole_l tl tm (kr,vr) tr c)
          | Gt, Lt => locate k tm $ ThreeMiddleHole_c tl (kl,vl) (kr,vr) tr c
          | _, Eq => inr ((kr,vr), ThreeRightHole_l tl (kl,vl) tm tr c)
          | _, Gt => locate k tr $ ThreeRightHole_c tl (kl,vl) tm (kr,vr) c
          end
      end.

    (* returns None if there are no elements in the tree.  otherwise,
       returns the greatest pair as well as either a single context if
       the element was a two node, or the pair's sibling and a context
       if it was a three node. *)
    Fixpoint locate_greatest (t:tree) (c:context)
        : option ((K*V) * (context + (K*V) * context)) :=
      match t with
      | Null_t => None
      | Two_t tl em tr =>
          locate_greatest tr (TwoRightHole_c tl em c)
          <|> Some (em, inl c)
      | Three_t tl el tm er tr =>
          locate_greatest tr (ThreeRightHole_c tl el tm er c)
          <|> Some (er, inr (el,c))
      end.

    Definition lookup (k:K) (t:tree) : option V :=
      match locate k t Top_c with
      | inl _ => None
      | inr ((_,v),_) => Some v
      end.

    (* if insertion results in a subtree which is too tall, propegate it up into
     * its context.
     *)
    Fixpoint insert_up (tet:tree * (K*V) * tree) (c:context) : tree :=
      let '(tl,em,tr) := tet in
      match c with
      (*     _          
       *     |          
       *    [em]    =>   [em]
       *   //  \\        /  \
       *  tl    tr      tl   tr
       *)
      | Top_c => Two_t tl em tr
      (*        c'              c'
       *        |               |
       *      [em']    =>    [em][em']
       *      /   \          /  |   \
       *    [em]   tr'     tl  tr   tr'
       *   // \\
       *  tl   tr
       *)
      | TwoLeftHole_c em' tr' c' => zip (Three_t tl em tr em' tr') c'
      (*     c'                c'
       *     |                 |
       *   [em']      =>    [em'][em]
       *   /   \            /  |   \
       *  tl'  [em]       tl'  tl   tr
       *      // \\
       *     tl   tr
       *)
      | TwoRightHole_c tl' em' c' => zip (Three_t  tl' em' tl em tr ) c'
      (*         c'                  c'
       *         |                   |
       *      [el][er]     =>      [el]
       *      /  |   \            //  \\
       *    [em] tm   tr'       [em]   [er]
       *   // \\                /  \   /  \
       *  tl   tr              tl  tr tm  tr'
       *)
      | ThreeLeftHole_c el tm er tr' c' => insert_up (Two_t tl em tr, el, Two_t tm er tr') c'
      (*      c'                 c'
       *      |                  |
       *   [el][er]     =>      [em]
       *   /   |  \            //  \\
       *  tl' [em] tr'       [el]   [er]
       *     // \\           /  \   /  \
       *    tl   tr         tl' tl tr  tr'
       *)
      | ThreeMiddleHole_c tl' el er tr' c' => insert_up (Two_t tl' el tl, em, Two_t tr er tr') c'
      (*      c'                   c'
       *      |                    |
       *   [el][er]       =>      [er]
       *   /  |   \              //  \\
       *  tl' tm  [em]         [el]   [em]
       *          // \\        /  \   /  \
       *         tl   tr      tl' tm tl  tr
       *)
      | ThreeRightHole_c tl' el tm er c' => insert_up (Two_t tl' el tm, er, Two_t tl em tr) c'
      end.

    (* insert an element into the two-three tree *)
    Definition insert_with (f:V -> V -> V) (k:K) (v:V) (t:tree) : tree :=
      match locate k t Top_c with
      | inl c => insert_up (Null_t, (k,v), Null_t) c
      | inr ((_,v'), l) => fill_location (k,f v v') l
      end.
    Definition insert_replace : K -> V -> tree -> tree :=
      insert_with const.
    Definition insert_keep : K -> V -> tree -> tree :=
      insert_with (flip const).

    (* update an element in the tree *)
    Definition update (k:K) (f:V -> V) (t:tree) : tree :=
      match locate k t Top_c with
      | inl c => t
      | inr ((_,v), l) => fill_location (k,f v) l
      end.

    (* if remove results in a tree which is too short, propegate the gap into the
     * context *)
    (* Returns None if the tree is not well formed *)
    Fixpoint remove_up (t:tree) (c:context) : option tree :=
      match c with
      (*  _        
       *  ||
       *  e  =>  e
       *)
      | Top_c => Some t
      (*    c'                    c'
       *    |                     |
       *   [em]           =>     [el']
       *  //  \                  /   \
       *  t  [el'][er']       [em]   [er']
       *     /   |   \        /  \    /  \
       *    tl'  tm'  tr'    t   tl' tm' tr'
       *) 
      | TwoLeftHole_c em (Three_t tl' el' tm' er' tr') c' =>
          Some $ zip (Two_t (Two_t t em tl') el' (Two_t tm' er' tr')) c'
      (*    c'                c'
       *    |                 || 
       *   [em]       =>   [em][em']
       *  //  \            /   |   \
       *  t   [em']       t    tl'  tr'
       *     /    \
       *    tl'   tr'
       *) 
      | TwoLeftHole_c em (Two_t tl' em' tr') c' =>
          remove_up (Three_t t em tl' em' tr') c'
      (*          c'             c'
       *          |              |
       *         [em]   =>      [er']
       *        /   \\          /   \
       *  [el'][er']  t     [el']   [em]
       *   /   |   \        /  \    /  \
       *  tl'  tm'  tr'    tl' tm' tr'  t
       *) 
      | TwoRightHole_c (Three_t tl' el' tm' er' tr') em c' =>
          Some $ zip (Two_t (Two_t tl' el' tm') er' (Two_t tr' em t)) c'
      (*        c'            c'
       *        |             || 
       *       [em]   =>   [em'][em]
       *       /  \\       /   |   \
       *    [em']  t      tl'  tr'  t  
       *   /    \     
       *  tl'   tr'
       *) 
      | TwoRightHole_c (Two_t tl' em' tr') em c' =>
          remove_up (Three_t tl' em' tr' em t) c'
      (*         c'                      c'
       *         |                       | 
       *      [el][er]      =>        [el][er]
       *   //    |     \             /   |    \
       *  t  [el'][er'] tr       [el']  [er']  tr
       *    /    |    \          /  \    /  \
       *   tl'   tm'  tr'       t   tl' tm' tr'
       *) 
      | ThreeLeftHole_c el (Three_t tl' el' tm' er' tr') er tr c' =>
          Some $ zip (Three_t (Two_t t el' tl') el (Two_t tm' er' tr') er tr) c'
      (*         c'                       c'
       *         |                        | 
       *      [el][er]      =>           [er]
       *   //    |     \                /    \
       *  t    [em']    tr        [el][em']   tr
       *       /   \             /    |    \
       *     tl'   tr'          t    tl'    tr'
       *) 
      | ThreeLeftHole_c el (Two_t tl' em' tr') er tr c' =>
          Some $ zip (Two_t (Three_t t el tl' em' tr') er tr) c'
      (*                c'                        c'
       *                |                         | 
       *             [el][er]      =>         [er'][er]
       *           /     ||   \              /    |    \
       *     [el'][er']  t     tr        [el']   [el]   tr
       *    /    |    \                  /  \    /  \    
       *  tl'   tm'   tr'              tl'  tm'  tr' t 
       *) 
      | ThreeMiddleHole_c (Three_t tl' el' tm' er' tr') el er tr c' =>
          Some $ zip (Three_t (Two_t tl' el' tm') er' (Two_t tr' el t) er tr) c'
      (*        c'                            c'
       *        |                             | 
       *     [el][er]             =>      [el][el']
       *   /    ||   \                  /    |     \
       *  tl    t  [el'][er']         tl   [er]     [er']
       *           /    |    \              /  \     /  \   
       *         tl'   tm'   tr'           t   tl'  tm'  tr'
       *) 
      | ThreeMiddleHole_c tl el er (Three_t tl' el' tm' er' tr') c' =>
          Some $ zip (Three_t tl el (Two_t t er tl') el' (Two_t tm' er' tr')) c'
      (*            c'                        c'
       *            |                         | 
       *         [el][er]      =>           [er]
       *       /     ||   \                /   \
       *    [em']    t     tr        [em'][el]  tr
       *    /  \                     /   |    \            
       *  tl'  tr'                 tl'  tr'    t   
       *) 
      | ThreeMiddleHole_c (Two_t tl' em' tr') el er tr c' =>
          Some $ zip (Two_t (Three_t tl' em' tr' el t) er tr) c'
      (*        c'                   c'
       *        |                    | 
       *     [el][er]        =>    [el]
       *   /    ||   \             /   \
       *  tl    t   [em']        tl   [er][em']
       *            /   \            /    |    \   
       *          tl'   tr'         t     tl'   tr'
       *) 
      | ThreeMiddleHole_c tl el er (Two_t tl' em' tr') c' =>
          Some $ zip (Two_t tl el (Three_t t er tl' em' tr')) c'
      (*         c'                  c'
       *         |                   | 
       *      [el][er]      =>     [el][er']
       *   /      |    \\         /   |     \
       *  tl [el'][er']  t      tl  [el']   [er]
       *     /   |     \           /   \    /   \
       *   tl'   tm'    tr'      tl'   tm' tr'   t
       *) 
      | ThreeRightHole_c tl el (Three_t tl' el' tm' er' tr') er c' =>
          Some $ zip (Three_t tl el (Two_t tl' el' tm') er' (Two_t tr' er t)) c'
      (*         c'                  c'
       *         |                   | 
       *      [el][er]      =>      [el]
       *     /    |   \\            /   \
       *    tl  [em']  t          tl  [em'][er]
       *        /   \                  /   |   \
       *      tl'    tr'              tl'  tr   t
       *) 
      | ThreeRightHole_c tl el (Two_t tl' em' tr') er c' =>
          Some $ zip (Two_t tl el (Three_t tl' em' tr' er t)) c'
      | TwoLeftHole_c _ Null_t _ => None
      | TwoRightHole_c Null_t _ _ => None
      | ThreeLeftHole_c _ Null_t _ _ _ => None
      | ThreeMiddleHole_c Null_t _ _ _ _ => None
      | ThreeRightHole_c _ _ Null_t _ _ => None
      end.

    (* returns None if the tree is not well formed *)
    Definition remove (k:K) (t:tree) : option (tree * option V) :=
      match locate k t Top_c with
      (* element doesn't exist *)
      | inl _ => Some (t, None)
      (* element found at location [loc] *)
      | inr ((_,v), loc) =>
          (fun t => (t, Some v)) <$> match loc with
          (* element found at a two-node *)
          | TwoHole_l tl tr c =>
              let mkContext g c' := TwoLeftHole_c g tr c' in
              match locate_greatest tl Top_c with
              (* no children: turn into a hole and propagate *)
              | None => remove_up Null_t c
              (* greatest leaf is a two-node: replace it with a hole and propagate *)
              | Some (g, inl c') => remove_up Null_t $ fuse (mkContext g c') c
              (* greatest leaf is a three-node: turn it into a two-node *)
              | Some (g, inr (el, c')) => Some $ zip (single el) $ fuse (mkContext g c') c
              end
          (* element found on left side of three-node *)
          | ThreeLeftHole_l tl tm er tr c =>
              let mkContext g c' := ThreeLeftHole_c g tm er tr c' in
              match locate_greatest tl Top_c with
              (* no children: turn into a two-node *)
              | None => Some $ zip (single er) c
              (* greatest leaf is a two-node: replace it with a hole and propagate *)
              | Some (g, inl c') => remove_up Null_t $ fuse (mkContext g c') c
              (* greatest leaf is a three-node: turn it into a two-node *)
              | Some (g, inr (el, c')) => Some $ zip (single el) $ fuse (mkContext g c') c
              end
          (* element found on right side of three-node *)
          | ThreeRightHole_l tl el tm tr c =>
              let mkContext g c' := ThreeMiddleHole_c tl el g tr c' in
              match locate_greatest tm Top_c with
              (* no children: turn into a two-node *)
              | None => Some $ zip (single el) c
              (* greatest leaf is a two-node: replace it with a hole and propagate *)
              | Some (g, inl c') => remove_up Null_t $ fuse (mkContext g c') c
              (* greatest leaf is a three-node: turn it into a two-node *)
              | Some (g, inr (el, c')) => Some $ zip (single el) $ fuse (mkContext g c') c
              end
          end
      end.


    Fixpoint to_list_k (t:tree) (k:list (K*V) -> list (K*V)) : list (K*V) :=
      match t with
      | Null_t => k nil
      | Two_t tl em tr =>
          to_list_k tl $ fun xl =>
            to_list_k tr $ fun xr =>
              k $ app xl (em::xr)
      | Three_t tl el tm er tr =>
          to_list_k tl $ fun xl =>
            to_list_k tm $ fun xm =>
              to_list_k tr $ fun xr =>
                k $ xl ** (el::xm) ** (er::xr)
      end.

    Definition to_list t := to_list_k t id.
    Definition tree_cofold {w A} `{! Counit w ,! Cobind w } (f:(K*V) -> w A -> A) (aW:w A) : tree -> A :=
      cofold f aW '.' to_list.
    Definition tree_mbuild {m} `{! FUnit m ,! MBind m } (f:forall {A}, ((K*V) -> A -> A) -> A -> m A) : m tree :=
      f (uncurry insert_replace) Null_t.
    Definition from_list : list (K*V) -> tree := iter (fun t kv => uncurry insert_replace kv t) Null_t.

    Definition union_with (f:V -> V -> V) (t1:tree) (t2:tree) : tree :=
      let fld (t:tree) (e:K*V) :=
        let (k,v) := e in
        insert_with f k v t
      in
      iter fld t2 $ to_list t1.

  End Context.
  Arguments tree : clear implicits.
  
  (* returns none if not well founded *)
  Definition difference {K V W} `{! TotalOrdDec K }
      (t1:tree K V) (t2:tree K W) : option (tree K V) :=
    let fld (t:tree K V) (e:K*W) : option (tree K V) :=
      let '(k,_) := e in
      fmap fst (remove k t)
    in
    miter fld t1 $ to_list t2.

  Definition intersect_with {K} `{! TotalOrdDec K } {V W X}
      (f:V -> W -> X) (t1:tree K V) (t2:tree K W) : tree K X :=
    let fld (t:tree K X) (e:K*W) : tree K X :=
      let (k,w) := e in
      match lookup k t1 with
      | None => t
      | Some v => insert_replace k (f v w) t
      end
    in iter fld empty $ to_list t2.

  Fixpoint map_with {K V W} (f:K -> V -> W) (t:tree K V) : tree K W :=
    match t with
    | Null_t => Null_t
    | Two_t tl em tr =>
        let (k,v) := em in
        Two_t (map_with f tl) (k,f k v) (map_with f tr)
    | Three_t tl el tm er tr =>
        let '((kl,vl),(kr,vr)) := (el, er) in
        Three_t (map_with f tl) (kl,f kl vl)
                (map_with f tm) (kr,f kr vr)
                (map_with f tr)
    end.

  Definition map {K V W} (f:V -> W) : tree K V -> tree K W := map_with $ const f.

  Definition size {K V} : tree K V -> N := length '.' to_list.

  Definition reduce {K V} `{! GUnit V ,! GTimes V } : tree K V -> V :=
    gproduct '.' List.map snd '.' to_list.

  Definition remove_unsafe {K} `{! TotalOrdDec K } {V} : K -> tree K V -> tree K V * option V :=
    from_option (empty, None) '.:' remove .

  Definition difference_unsafe {K} `{! TotalOrdDec K } {V W} : tree K V -> tree K W -> tree K V :=
    from_option empty '.:' difference.

  Definition set_map {A B} `{! TotalOrdDec B } (f:A -> B) (t:tree A unit) : tree B unit :=
    let fld (t:tree B unit) (e:A*unit) : tree B unit :=
      insert_with const (f (fst e)) tt t
    in
    foldl fld empty $ to_list t.

  Definition set_empty {A} : tree A unit := empty.
  Definition set_singleton {A} (a:A) : tree A unit := singleton a tt.
  Definition set_member {A} `{! TotalOrdDec A } (a:A) (t:tree A unit) : bool :=
    match lookup a t with
    | None => false
    | Some tt => true
    end.
  Definition set_insert {A} `{! TotalOrdDec A } (a:A) (t:tree A unit) : tree A unit :=
    insert_with (const id) a tt t.
  Definition set_remove {A} `{! TotalOrdDec A } (a:A) (t:tree A unit)
      : option (tree A unit * bool) :=
    match remove a t with
    | None => None
    | Some (t,r) => Some $ (fun x => (t,x)) $
        match r with
        | None => false
        | Some _ => true
        end
    end.
  Definition set_remove_unsafe {A} `{! TotalOrdDec A } (a:A) (t:tree A unit)
      : tree A unit * bool :=
    match set_remove a t with
    | None => (empty, false)
    | Some x => x
    end.

  Definition set_unionl {A} `{! TotalOrdDec A }
      : tree A unit -> tree A unit -> tree A unit :=
    union_with const.

  Definition set_difference {A} `{! TotalOrdDec A }
      : tree A unit -> tree A unit -> option (tree A unit) :=
    difference.

  Definition set_difference_unsafe {A} `{! TotalOrdDec A }
      : tree A unit -> tree A unit -> tree A unit :=
    difference_unsafe.

  Definition set_intersect {A} `{! TotalOrdDec A }
      : tree A unit -> tree A unit -> tree A unit :=
    intersect_with const.

  Definition set_size {A} : tree A unit -> N := size.

  Definition set_reduce {A} `{! GUnit A ,! GTimes A } : tree A unit -> A :=
    gproduct '.' List.map fst '.' to_list.

  Definition set_from_list {A} `{! TotalOrdDec A } : list A -> tree A unit :=
    from_list '.' List.map (fun a => (a, tt)).

  Definition set_to_list {A} : tree A unit -> list A :=
    List.map fst '.' to_list.

  Definition set_cofold {A w} `{! Counit w ,! Cobind w } {B} (f:A -> w B -> B) : w B -> tree A unit -> B :=
    tree_cofold (fun att bW => let (a,tt) := att in f a bW).

  Definition set_mbuild {A} `{! TotalOrdDec A } {m} `{ FUnit m, MBind m } (ff:forall {C}, (A -> C -> C) -> C -> m C) : m (tree A unit) :=
    tree_mbuild (fun _ f' => ff $ fun a => f' (a,tt)).

  Fixpoint sequence {K} {u} `{! FUnit u ,! FApply u } {V} (tT : tree K (u V)) : u (tree K V) := 
    match tT with
    | Null_t => funit Null_t
    | Two_t tl em tr =>
        funit Two_t
        <@> sequence tl
        <@> sequence_snd em
        <@> sequence tr
    | Three_t tl el tm er tr =>
        funit Three_t
        <@> sequence tl
        <@> sequence_snd el
        <@> sequence tm
        <@> sequence_snd er
        <@> sequence tr
    end.

  Definition set_sequence {u} `{! FUnit u ,! FApply u } {A} `{! TotalOrdDec A }
      : tree (u A) unit -> u (tree A unit) :=
    fapply_fmap set_from_list '.' tsequence '.' set_to_list.
End TwoThreeTrees.
Definition two3map := TwoThreeTrees.tree.
Definition two3set := flip two3map unit.
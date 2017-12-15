open Expr
open List
open Util

let mk_log level = mk_logger "Norm.NormField" level "NormField.ml"
let log_i  = mk_log Bolt.Level.INFO


let rec zip xs ys =
    match (xs, ys) with
    | (x::xs', y::ys') -> 
            (match (zip xs' ys') with
            | Some k -> Some ((x,y) :: k)
            | None -> None)
    | ([], []) -> Some []
    | (_, _) -> None

let rec remove_by (f : 'a -> bool) (xs : 'a list) =
    match xs with
    | [] -> (None, [])
    | (x :: xs') ->
            if f x then (Some x, xs') else let p = remove_by f xs' in (fst p, x :: (snd p))
           
let rec is_bijection_by (comp : 'a -> 'a -> bool) (xs : 'a list) (ys : 'a list) =
    match xs with
    | [] -> (match ys with | [] -> true | _ -> false)
    | x :: xs' ->
            (match (remove_by (comp x) ys) with
            | (Some _, ys') -> is_bijection_by comp xs' ys'
            | (None, ys) -> false)

module type MATDATA = sig
        type elt
        type shape
        val mult_shape : shape -> shape -> shape
        val concat_shape : shape -> shape -> shape
        val sl_shape : shape -> shape
        val sr_shape : shape -> shape
        val trans_shape : shape -> shape
        
        val elt_eq : elt -> elt -> bool
        val shape_eq : shape -> shape -> bool

        val shape_of_elt : elt -> shape

        val elt_of_expr : expr -> elt

        type mat =
            | MPlus of mat list
            | MOpp of mat
            | MMult of mat * mat
            | MTrans of mat
            | MConcat of mat * mat
            | MSplitLeft of mat
            | MSplitRight of mat
            | MId of shape
            | MZero of shape
            | MBase of elt
        


        val mat_of_expr : expr -> mat
        val expr_of_mat : mat -> expr

    end

module type MATRULES = functor (Data : MATDATA) -> sig
    val norm_mat: Data.mat -> Data.mat
end

module MkMat : MATRULES = functor (Data : MATDATA) -> struct

    open Data

    (* TODO: let below take as argument extra rewrite rules, which ListMat can
     * hook into. *) 
    let rec norm_mat (m : Data.mat) : Data.mat = 

        let rec mat_eq  (m1 : mat) (m2 : mat) =
            match (m1,m2) with
            | (MPlus xs, MPlus ys) -> 
                    is_bijection_by mat_eq xs ys
            | (MOpp x, MOpp y) -> mat_eq x y
            | (MMult (x,y), MMult (x',y')) -> (mat_eq x x') && (mat_eq y y')
            | (MTrans x, MTrans y) -> mat_eq x y
            | (MConcat (x,y), MConcat (x', y')) -> (mat_eq x x') && (mat_eq y y')
            | (MSplitLeft x, MSplitLeft y) -> mat_eq x y
            | (MSplitRight x, MSplitRight y) -> mat_eq x y
            | (MId s1, MId s2) -> Data.shape_eq s1 s2
            | (MZero s1, MZero s2) -> Data.shape_eq s1 s2
            | (MBase x, MBase y) -> Data.elt_eq x y
            | _ -> false in

        let rec shape_of_mat (m : mat) : shape =
            match m with
            | MPlus xs -> shape_of_mat (List.hd xs)
            | MOpp x -> shape_of_mat x
            | MMult (x,y) -> Data.mult_shape (shape_of_mat x) (shape_of_mat y)
            | MTrans x -> Data.trans_shape (shape_of_mat x)
            | MConcat (x,y) -> Data.concat_shape (shape_of_mat x) (shape_of_mat y)
            | MSplitLeft x -> Data.sl_shape (shape_of_mat x)
            | MSplitRight x -> Data.sr_shape (shape_of_mat x)
            | MId s -> s
            | MZero s -> s
            | MBase e -> Data.shape_of_elt e in

        let flatten_plus (xs : mat list) =
            let (plusses, others) = fold_left (fun acc x ->
                (match x with
                | MPlus ys -> ((fst acc) @ ys, snd acc)
                | e -> (fst acc, e :: (snd acc)))) ([], []) xs in
            plusses @ others in

        let mat_is_zero (m : mat) = match m with | MZero _ -> true | _ -> false
        in
         
        (* given a list, remove pairs that are opposites of each other. *)
        let rec mat_remove_opps (xs : mat list) =
            match xs with
            | [] -> []
            | ((MOpp x) :: xs') ->
                    (match (remove_by (mat_eq x) xs') with
                    | (Some _, xs'') -> mat_remove_opps xs''
                    | (None,_) -> (MOpp x) :: (mat_remove_opps xs'))
            | (x :: xs') ->
                    (match (remove_by (mat_eq (MOpp x)) xs') with
                    | (Some _, xs'') -> mat_remove_opps xs''
                    | (None, _) -> x :: (mat_remove_opps xs')) in

        let is_concatpair (x : mat) (y : mat) =
            match (x,y) with
            | (MConcat (a,b), MConcat (c,d)) ->
                    Data.shape_eq (shape_of_mat a) (shape_of_mat c) &&
                    Data.shape_eq (shape_of_mat b) (shape_of_mat d) 
            | _ -> false in

        let combine_concatpair (x : mat) (y : mat) =
            match (x,y) with
            | (MConcat (a,b), MConcat (c,d)) ->
                    MConcat (MPlus [a;c], MPlus [b;d])
            | _ -> assert false in

        let rec combine_concats_aux (x : mat) (xs : mat list) : mat * (mat list) =
            match xs with
            | [] -> (x, [])
            | (x' :: xs') ->
                    if is_concatpair x x' then 
                        combine_concats_aux (combine_concatpair x x') xs'
                    else
                        let (a,b) = combine_concats_aux x xs' in
                        (a, x' :: b) in
        
        let rec combine_concats (xs : mat list) : mat list =
            match xs with
            | [] -> []
            | x :: xs ->
                    let (x', xs') = combine_concats_aux x xs in
                    x' :: (combine_concats xs') in

        let rewrite_plus (xs : mat list) : mat =
            let xs = flatten_plus xs in
            let xs = List.filter (fun x -> not (mat_is_zero x)) xs in
            let xs = mat_remove_opps xs in
            let xs = combine_concats xs in
            match (List.length xs) with
            | 0 -> MZero (shape_of_mat (List.hd xs))
            | _ -> MPlus xs in

        
        let is_splitpair x y =
            match x,y with
            | MSplitLeft x', MSplitRight y' -> mat_eq x' y'
            | _ -> assert false
        in

        let rec accum_splitpair (so_far : mat list) (sls : mat list) (srs : mat list) =
            match sls, srs with
            | [], [] -> (so_far, [], [])
            | [], srs -> (so_far, [], srs)
            | sl::sls, srs ->
                    match (remove_by (is_splitpair sl) srs) with
                    | (Some _, srs) ->
                            let e = (match sl with | MSplitLeft x -> x | _ -> assert
                            false) in
                            accum_splitpair (e :: so_far) sls srs
                    | (None, srs) ->
                            let (a,b,c) = accum_splitpair so_far sls srs in
                            (a, sl::b, c)
        in

        let rem_splitpairs xs ys =
            let (sl_xs, xs') = List.partition (fun x -> match x with | MSplitLeft _ ->
                true | _ -> false) xs in
            let (sr_ys, ys') = List.partition (fun x -> match x with | MSplitRight _ ->
                true | _ -> false) ys in
            let (matched_pairs, sls, srs) = accum_splitpair [] sl_xs sr_ys in
            (matched_pairs, sls @ xs', srs @ ys')
        in
        
        let mat_concatplus_simpl xs ys =
            let (pairs, xs, ys) = rem_splitpairs xs ys in
            match pairs with
            | [] -> MConcat ((MPlus xs), (MPlus ys))
            | _ -> MPlus (pairs @ [MConcat ((MPlus xs), (MPlus ys))])
        in

        (* Note this doesn't take into account ListOf reductions for lists, which must be done
         * separately *)
        let matsig_rewrite_step (m : mat) =
            match m with
            | MMult (a, MMult (b,c)) -> MMult (MMult (a,b), c)
            | MMult (MId _, a) -> a
            | MMult (a, MId _) -> a
            | MMult (MZero p, a) -> MZero (Data.mult_shape p (shape_of_mat a))
            | MMult (a, MZero p) -> MZero (Data.mult_shape (shape_of_mat a) p)
            | MMult (MOpp a, MOpp b) -> MMult (a,b)
            | MMult (MOpp a, b) -> MOpp (MMult (a,b))
            | MMult (a, MOpp b) -> MOpp (MMult (a,b))
            | MMult (a, MConcat (b,c)) -> MConcat (MMult (a,b), MMult (a,c))
            | MMult (MPlus xs, y) -> MPlus (map (fun x -> MMult (x,y)) xs)
            | MMult (y, MPlus xs) -> MPlus (map (fun x -> MMult (y,x)) xs)
            | MOpp (MOpp e) -> e
            | MOpp (MPlus xs) -> MPlus (map (fun x -> MOpp x) xs)
            | MTrans (MMult (a,b)) -> MMult (MTrans b, MTrans a)
            | MTrans (MOpp a) -> MOpp (MTrans a)
            | MTrans (MPlus xs) -> MPlus (map (fun x -> MTrans x) xs)
            | MTrans (MTrans a) -> a
            | MPlus xs -> rewrite_plus xs
            | MConcat (MSplitLeft a, MSplitRight b) -> 
                    if mat_eq a b then a else m
            | MConcat (MZero p1, MZero p2) ->
                    MZero (Data.concat_shape p1 p2)
            | MConcat (MOpp a, MOpp b) ->
                    MOpp (MConcat (a,b))
            | MConcat (MPlus xs, MPlus ys) -> mat_concatplus_simpl xs ys
            | MSplitLeft (MOpp a) -> MOpp (MSplitLeft a)
            | MSplitLeft (MPlus xs) -> MPlus (map (fun x -> MSplitLeft x) xs)
            | MSplitLeft (MConcat (a,_)) -> a
            | MSplitLeft (MMult (a,b)) -> MMult (a, MSplitLeft b)
            | MSplitRight (MOpp a) -> MOpp (MSplitRight a)
            | MSplitRight (MPlus xs) -> MPlus (map (fun x -> MSplitRight x) xs)
            | MSplitRight (MConcat (_,b)) -> b
            | MSplitRight (MMult (a,b)) -> MMult (a, MSplitRight b)
            | _ -> m
        in

        
        let norm_matsig_rec (nf : mat -> mat) (m : mat) =
            match m with
            | MPlus xs -> MPlus (map nf xs)
            | MOpp x -> MOpp (nf x)
            | MMult (x,y) -> MMult (nf x, nf y)
            | MTrans x -> MTrans (nf x)
            | MConcat (x,y) -> MConcat (nf x, nf y)
            | MSplitLeft x -> MSplitLeft (nf x)
            | MSplitRight x -> MSplitRight (nf x)
            | _ -> m
        in

        let next = matsig_rewrite_step (norm_matsig_rec norm_mat m) in
        if (mat_eq m next) then m else norm_mat next
    
end




    (* depreciated code; will go in MATDATA implementations
 *
 *
let rec mdim_of_matsig (f : 'a -> Type.mdim * Type.mdim) (m : 'a matsig) : Type.mdim *
Type.mdim =
    match m with
    | MPlus xs -> mdim_of_matsig f (List.hd xs)
    | MOpp x -> mdim_of_matsig f x
    | MMult (x,y) -> (fst (mdim_of_matsig f x), snd (mdim_of_matsig f y))
    | MTrans x -> let p = mdim_of_matsig f x in (snd p, fst p)
    | MConcat (x,y) -> (fst (mdim_of_matsig f x), Type.MDPlus (snd (mdim_of_matsig f x), snd (mdim_of_matsig f y)))
    | MSplitLeft x -> let p = mdim_of_matsig f x in
                      (match (snd p) with
                      | Type.MDPlus (a, _) -> (fst p, a)
                      | _ -> failwith "bad split")
    | MSplitRight x -> let p = mdim_of_matsig f x in
                      (match (snd p) with
                      | Type.MDPlus (_, a) -> (fst p, a)
                      | _ -> failwith "bad split")
    | MId d -> d
    | MZero d -> d
    | MBase a -> f a



let mk_listbase_eq (eqA : 'a -> 'a -> bool) (eqB : 'b -> 'b -> bool) (x : ('a,
'b) listbase) (y: ('a, 'b) listbase) =
    match x,y with
    | LBase a, LBase b -> eqA a b
    | LOf (d,a), LOf (d',b) -> (d == d') && (comp_matsig eqB a b)
    | _, _ -> false

let mk_listbase_dim (fA : 'a -> Type.mdim * Type.mdim) (fB : 'b -> Type.mdim *
Type.mdim) m =
    match m with
    | LBase a -> fA a
    | LOf (d,b) -> mdim_of_matsig fB b

let rec listlen_of_matsig (f : 'a -> Type.mdim) (m : ('a,'b) listbase matsig) :
    Type.mdim =
        match m with
        | MPlus xs -> listlen_of_matsig f (List.hd xs)
        | MOpp x -> listlen_of_matsig f x
        | MMult (x,y) -> listlen_of_matsig f x
        | MTrans x -> listlen_of_matsig f x
        | MConcat (x,y) -> listlen_of_matsig f x
        | MSplitLeft x -> listlen_of_matsig f x
        | MSplitRight x -> listlen_of_matsig f x
        | MId d -> failwith "Id of list type"
        | MZero d -> failwith "mzero of list type"
        | MBase (LBase a) -> f a
        | MBase (LOf (d,a)) -> d




let rec matsig_of_mat_expr (e : expr) : expr matsig = 
    match e.e_node with
    | App(MatMult, [e1;e2]) -> MMult (matsig_of_mat_expr e1, matsig_of_mat_expr
    e2)
    | App(MatOpp, [e]) -> MOpp (matsig_of_mat_expr e)
    | App(MatTrans, [e]) -> MTrans (matsig_of_mat_expr e)
    | App(MatConcat, [e1;e2]) -> MConcat (matsig_of_mat_expr e1,
    matsig_of_mat_expr e2)
    | App(MatSplitLeft, [e]) -> MSplitLeft (matsig_of_mat_expr e)
    | App(MatSplitRight, [e]) -> MSplitRight (matsig_of_mat_expr e)
    | Nary(MatPlus, es) -> MPlus (map matsig_of_mat_expr es)
    | Cnst(MatZero) -> let p = Type.dim_of_mat (e.e_ty) in MZero p
    | Cnst(MatId) -> MId (Type.dim_of_mat (e.e_ty))
    | _ -> MBase e

let rec mat_expr_of_matsig (m : expr matsig) : expr =
    match m with
    | MPlus ms -> 
            mk_MatPlus (map mat_expr_of_matsig ms)
    | MOpp m -> mk_MatOpp (mat_expr_of_matsig m)
    | MMult (m1,m2) -> mk_MatMult (mat_expr_of_matsig m1) (mat_expr_of_matsig
    m2)
    | MTrans m -> mk_MatTrans (mat_expr_of_matsig m)
    | MConcat (m1,m2) -> mk_MatConcat (mat_expr_of_matsig m1)
    (mat_expr_of_matsig m2)
    | MSplitLeft m -> mk_MatSplitLeft (mat_expr_of_matsig m)
    | MSplitRight m -> mk_MatSplitRight (mat_expr_of_matsig m)
    | MZero p -> mk_MatZero (fst p) (snd p)
    | MId p -> mk_MatId (fst p) (snd p)
    | MBase e -> e

    
let rec matsig_of_matlist_expr (e : expr) :
    (expr,expr) listbase matsig = 
    match e.e_node with
    | App(ListOp MatMult, [e1;e2]) -> MMult (matsig_of_matlist_expr e1, matsig_of_matlist_expr
    e2)
    | App(ListOp MatOpp, [e]) -> MOpp (matsig_of_matlist_expr e)
    | App(ListOp MatTrans, [e]) -> MTrans (matsig_of_matlist_expr e)
    | App(ListOp MatConcat, [e1;e2]) -> MConcat (matsig_of_matlist_expr e1,
    matsig_of_matlist_expr e2)
    | App(ListOp MatSplitLeft, [e]) -> MSplitLeft (matsig_of_matlist_expr e)
    | App(ListOp MatSplitRight, [e]) -> MSplitRight (matsig_of_matlist_expr e)
    | Nary(ListNop MatPlus, es) -> MPlus (map matsig_of_matlist_expr es)
    | App(ListOf, [e]) -> MBase (LOf (fst (Type.get_list_ty e.e_ty), matsig_of_mat_expr e))
    | _ -> MBase (LBase e)


let rec matlist_expr_of_matsig (m : (expr, expr) listbase matsig) : expr = 
    match m with
    | MPlus ms -> 
            mk_MatPlus (map matlist_expr_of_matsig ms)
    | MOpp m -> mk_MatOpp (matlist_expr_of_matsig m)
    | MMult (m1,m2) -> mk_MatMult (matlist_expr_of_matsig m1) (matlist_expr_of_matsig
    m2)
    | MTrans m -> mk_MatTrans (matlist_expr_of_matsig m)
    | MConcat (m1,m2) -> mk_MatConcat (matlist_expr_of_matsig m1)
    (matlist_expr_of_matsig m2)
    | MSplitLeft m -> mk_MatSplitLeft (matlist_expr_of_matsig m)
    | MSplitRight m -> mk_MatSplitRight (matlist_expr_of_matsig m)
    | MZero p -> failwith "mzero in list"
    | MId p -> failwith "mid in list"
    | MBase (LBase e) -> e
    | MBase (LOf (d,e)) -> mk_ListOf d (mat_expr_of_matsig e)




let matsig_list_rewrite_step (f : ('a,'b) listbase -> Type.mdim * Type.mdim) (m : (('a,'b) listbase) matsig) =
    match m with
    | MMult (MBase (LOf (d,a)), MBase (LOf (d',b))) -> MBase (LOf (d, MMult (a,b)))
    | MPlus [MBase (LOf (d,a)); MBase (LOf (d',b))] -> MBase (LOf (d, MPlus [a;b]))
    | MMult (MBase (LOf (d, MId _)), a) -> a
    | MMult (a, MBase (LOf (d, MId _))) -> a
    | MMult (MBase (LOf (d, MZero p)), a) -> (MBase (LOf (d, MZero (fst p, snd (mdim_of_matsig f a)))))
    | MMult (a, MBase (LOf (d, MZero p))) -> (MBase (LOf (d, MZero (fst
    (mdim_of_matsig f a), snd p))))
    | MConcat (MBase (LOf (d, MZero p1)), MBase (LOf (d', MZero p2))) ->
            MBase (LOf (d, MZero (fst p1, Type.MDPlus (snd p1, snd p2))))
    | _ -> m



let norm_matlist_rec (nf : 'a matsig -> 'a matsig) (m : (('a,'b) listbase)
matsig) =
    match m with
    | MBase (LOf (d,e)) -> MBase (LOf (d, nf e))
    | _ -> m



let rec norm_listmatsig (eqA : 'a -> 'a -> bool) (eqB : 'b -> 'b -> bool) 
                        (fA : 'a -> Type.mdim * Type.mdim) (fB : 'b -> Type.mdim * Type.mdim)  
                        (m: (('a,'b) listbase) matsig)
                        : (('a,'b) listbase) matsig =
    let nf = norm_listmatsig eqA eqB fA fB in
    let recurs x = norm_matlist_rec (norm_matsig eqB fB) (norm_matsig_rec nf x) in
    let next = matsig_list_rewrite_step (mk_listbase_dim fA fB) (matsig_rewrite_step (mk_listbase_eq eqA eqB) (mk_listbase_dim fA fB) (recurs m)) in
    if (comp_matsig (mk_listbase_eq eqA eqB) m next) then m else nf next
*)

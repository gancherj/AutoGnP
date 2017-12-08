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


type 'a matsig =
    | MPlus of ('a matsig) list
    | MOpp of ('a matsig)
    | MMult of ('a matsig) * ('a matsig)
    | MTrans of 'a matsig
    | MConcat of ('a matsig) * ('a matsig)
    | MSplitLeft of 'a matsig
    | MSplitRight of 'a matsig
    | MId of (Type.mdim * Type.mdim)
    | MZero of (Type.mdim * Type.mdim)
    | MBase of 'a (* variables, uninterpreted functions, ... *)

let rec comp_matsig (f : 'a -> 'a -> bool) (m1 : 'a matsig) (m2 : 'a matsig) =
    match (m1,m2) with
    | (MPlus xs, MPlus ys) -> 
            is_bijection_by (comp_matsig f) xs ys
    | (MOpp x, MOpp y) -> comp_matsig f x y
    | (MMult (x,y), MMult (x',y')) -> (comp_matsig f x x') && (comp_matsig f y y')
    | (MTrans x, MTrans y) -> comp_matsig f x y
    | (MConcat (x,y), MConcat (x', y')) -> (comp_matsig f x x') && (comp_matsig f y y')
    | (MSplitLeft x, MSplitLeft y) -> comp_matsig f x y
    | (MSplitRight x, MSplitRight y) -> comp_matsig f x y
    | (MId (a,b), MId (c,d)) -> (a == c) && (b == d)
    | (MZero (a,b), MZero (c,d)) -> (a == c) && (b == d)
    | (MBase x, MBase y) -> f x y
    | _ -> false

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

    
let matsig_of_matlist_expr (_ : expr) : expr matsig = failwith "unimp"
let matlist_expr_of_matsig (_ : expr matsig) : expr = failwith "unimp"

let matsig_flatten_plus (xs : ('a matsig) list) : ('a matsig) list =
    let (plusses, others) = fold_left (fun acc x -> 
        (match x with
        | MPlus ys -> ((fst acc) @ ys, snd acc)
        | e -> (fst acc, e :: (snd acc)))) ([],[]) xs in
    plusses @ others

let matsig_is_zero (m : 'a matsig) =
    match m with
    | MZero _ -> true
    | _ -> false


let rec matsig_remove_opps (eq : 'a -> 'a -> bool) (xs : ('a matsig) list) =
    match xs with
    | [] -> []
    | ((MOpp x) :: xs') ->
            (match (remove_by (comp_matsig eq x) xs') with
            | (Some _, xs'') -> matsig_remove_opps eq xs''
            | (None, _) -> (MOpp x) :: (matsig_remove_opps eq xs'))
    | (x :: xs') ->
            (match (remove_by (comp_matsig eq (MOpp x)) xs') with
            | (Some (_), xs'') -> matsig_remove_opps eq xs''
            | (None, _) -> x :: (matsig_remove_opps eq xs'))

let mdims_equal p1 p2 =
    (Type.mdim_equal (fst p1) (fst p2)) && (Type.mdim_equal (snd p1) (snd p2))


let is_concatpair f x y =
    match (x,y) with
    | (MConcat (a,b), MConcat (c,d)) ->
            (mdims_equal (mdim_of_matsig f a) (mdim_of_matsig f c))
            && (mdims_equal (mdim_of_matsig f b) (mdim_of_matsig f d))
    | _ -> false

let combine_concatpair x y =
    match (x,y) with
    | (MConcat (a,b), MConcat (c,d)) ->
            MConcat (MPlus [a;c], MPlus [b;d])
    | _ -> assert false


let rec combine_concats_aux f x xs =
    match xs with
    | [] -> (x, [])
    | (x' :: xs') ->
            if is_concatpair f x x' then
                let x'' = combine_concatpair x x' in
                combine_concats_aux f x'' xs'
            else
                let (a,b) = combine_concats_aux f x xs' in
                (a, x' :: b)

let rec matsig_combine_concats (f : 'a -> Type.mdim * Type.mdim) (xs : ('a matsig) list) =
    match xs with
    | [] -> []
    | x :: xs ->
            let (x', xs') = combine_concats_aux f x xs in 
            x' :: (matsig_combine_concats f xs')


let matsig_rewrite_plus (eq : 'a -> 'a -> bool) (f : 'a -> Type.mdim * Type.mdim) (xs : ('a matsig) list) : 'a matsig =
    let xs = matsig_flatten_plus xs in
    let xs = List.filter (fun x -> not (matsig_is_zero x)) xs in
    let xs = matsig_remove_opps eq xs in
    let xs = matsig_combine_concats f xs in
    match (List.length xs) with
    | 0 -> MZero (mdim_of_matsig f (List.hd xs))
    | _ -> MPlus xs


let is_splitpair eq sl sr =
    match sl,sr with
    | MSplitLeft x, MSplitRight y -> comp_matsig eq x y
    | _ -> assert false


let rec accum_splitpair eq so_far sls srs =
    match sls, srs with
    | [], [] -> (so_far, [], [])
    | [], srs -> (so_far, [], srs)
    | sl::sls, srs ->
            match (remove_by (is_splitpair eq sl) srs) with
            | (Some (_), srs) ->
                    let e = (match sl with | MSplitLeft x -> x | _ -> assert
                    false) in
                    accum_splitpair eq (e :: so_far) sls srs
            | (None, srs) ->
                    let (a,b,c) = accum_splitpair eq so_far sls srs in
                    (a, sl::b, c)


let rem_splitpairs eq xs ys =
    let (sl_xs, xs') = List.partition (fun x -> match x with | MSplitLeft _ ->
        true | _ -> false) xs in
    let (sr_ys, ys') = List.partition (fun x -> match x with | MSplitRight _ ->
        true | _ -> false) ys in
    let (matched_pairs, sls, srs) = accum_splitpair eq [] sl_xs sr_ys in
    (matched_pairs, sls @ xs', srs @ ys')
    
let matsig_concatplus_simpl eq xs ys =
    let (pairs, xs, ys) = rem_splitpairs eq xs ys in
    match pairs with
    | [] -> MConcat ((MPlus xs), (MPlus ys))
    | _ -> MPlus (pairs @ [MConcat ((MPlus xs), (MPlus ys))])





let matsig_rewrite_step (eq : 'a -> 'a -> bool) (f : 'a -> Type.mdim * Type.mdim) (m : 'a matsig) =
    match m with
    | MMult (a, MMult (b,c)) -> MMult (MMult (a,b), c)
    | MMult (MId _, a) -> a
    | MMult (a, MId _) -> a
    | MMult (MZero p, a) -> MZero (fst p, snd (mdim_of_matsig f a))
    | MMult (a, MZero p) -> MZero (fst (mdim_of_matsig f a), snd p)
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
    | MPlus xs -> matsig_rewrite_plus eq f xs
    | MConcat (MSplitLeft a, MSplitRight b) -> 
            if comp_matsig eq a b then a
            else m
    | MConcat (MZero p1, MZero p2) ->
            MZero (fst p1, Type.MDPlus (snd p1, snd p2))
    | MConcat (MOpp a, MOpp b) ->
            MOpp (MConcat (a,b))
    | MConcat (MPlus xs, MPlus ys) -> matsig_concatplus_simpl eq xs ys
    | MSplitLeft (MOpp a) -> MOpp (MSplitLeft a)
    | MSplitLeft (MPlus xs) -> MPlus (map (fun x -> MSplitLeft x) xs)
    | MSplitLeft (MConcat (a,_)) -> a
    | MSplitLeft (MMult (a,b)) -> MMult (a, MSplitLeft b)
    | MSplitRight (MOpp a) -> MOpp (MSplitRight a)
    | MSplitRight (MPlus xs) -> MPlus (map (fun x -> MSplitRight x) xs)
    | MSplitRight (MConcat (_,b)) -> b
    | MSplitRight (MMult (a,b)) -> MMult (a, MSplitRight b)
    | _ -> m

    
let norm_matsig_ (nf : 'a matsig -> 'a matsig) (m : 'a matsig) =
    match m with
    | MPlus xs -> MPlus (map nf xs)
    | MOpp x -> MOpp (nf x)
    | MMult (x,y) -> MMult (nf x, nf y)
    | MTrans x -> MTrans (nf x)
    | MConcat (x,y) -> MConcat (nf x, nf y)
    | MSplitLeft x -> MSplitLeft (nf x)
    | MSplitRight x -> MSplitRight (nf x)
    | MId p -> MId p
    | MZero e -> MZero e
    | MBase e -> MBase e

let rec norm_matsig (eq : 'a -> 'a -> bool) (f : 'a -> Type.mdim * Type.mdim) (m : 'a matsig) : 'a matsig = 
    let nf = norm_matsig eq f in
    let next = matsig_rewrite_step eq f (norm_matsig_ nf m) in
    if (comp_matsig eq m next) then m else 
        nf next
    




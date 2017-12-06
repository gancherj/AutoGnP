open Expr
open Type
open ExprUtils
open Util


let mk_log level = mk_logger "Deduce.Deduc" level "Deduc.ml"

let rec rem_first_occ f xs = match xs with
| [] -> []
| x :: xs -> if (f x) then xs else x :: (rem_first_occ f xs)

let rec rem_first_eq e xs = match xs with
| [] -> []
| x :: xs -> if (x = e) then xs else x :: (rem_first_eq e xs)

(* find instances of e and -e in es, and remove the pair if found *)

let is_zero e = match e.e_node with Cnst(ListOf MatZero) -> true | _ -> false

let is_opp_sym e e' = (e = (mk_ListMatOpp e')) || ((mk_ListMatOpp e) = e')

let contains_op e es = List.exists (fun x -> is_opp_sym e x) es

let rec rem_first_op x es = match es with
    | [] -> []
    | e :: es' -> if is_opp_sym x e then es' else e :: (rem_first_op x es')

let rem_opps_step so_far e = 
    if contains_op e so_far then 
        let es = rem_first_op e so_far in
        es
    else
        e :: so_far

let remove_opps es =
    List.fold_left rem_opps_step [] es



let is_splitleft e = match e.e_node with App(ListOp MatSplitLeft, _) -> true | _ -> false

let extract_splitleft e = match e.e_node with 
    | App(ListOp MatSplitLeft, [e]) -> e 
    | _ -> assert false

let is_splitright e = match e.e_node with App(ListOp MatSplitRight, _) -> true | _ -> false

let extract_splitright e = match e.e_node with 
    | App(ListOp MatSplitRight, [e]) -> e 
    | _ -> assert false

let is_splitpair sl sr = (extract_splitleft sl) = (extract_splitright sr)

let contains_splitpair sl srs = List.exists (is_splitpair sl) srs

let rec accum_splitpair so_far sls srs = match sls, srs with
    | [], [] -> (so_far, [], []) (* so_far = matched deconstructed pairs, sls left, srs left *)
    | [], srs -> (so_far, [], srs)
    | sl :: sls, srs ->
        if contains_splitpair sl srs then
            let srs = rem_first_occ (is_splitpair sl) srs in
            let e = extract_splitleft sl in
            accum_splitpair (e :: so_far) sls srs
        else
            let (a,b,c) = accum_splitpair so_far sls srs in
            (a, sl :: b, c)

let rem_splitpairs es1 es2 =
    let (sl_es1, es1') = List.partition (is_splitleft) es1 in
    let (sr_es2, es2') = List.partition (is_splitright) es2 in
    let (matched_pairs, sls, srs) = accum_splitpair [] sl_es1 sr_es2 in
    (matched_pairs, sls @ es1', srs @ es2')

(* helper functions for a||b + c||d -> (a+c) || (b+d) *)

let is_concatpair e1 e2 = (* if e1 = a||b, e2 = c||d, and dim(a) = dim(b),
dim(c) = dim(d) *)
    match e1.e_node, e2.e_node with
    | App(ListOp MatConcat, [e11;e12]), App(ListOp MatConcat, [e21;e22]) ->
    let ((n11,m11), (n12,m12),(n21,m21),(n22,m22)) = (get_mat_mdims e11.e_ty,
    get_mat_mdims e12.e_ty, get_mat_mdims e21.e_ty, get_mat_mdims e22.e_ty) in
    mdim_equal n11 n21 && mdim_equal m11 m21 && mdim_equal n12 n22 && mdim_equal
    m12 m22
    | _ -> false

let combine_concatpair e1 e2 =
    match e1.e_node, e2.e_node with
    | App(ListOp MatConcat, [e11;e12]), App(ListOp MatConcat, [e21;e22]) ->
            mk_ListMatConcat  (mk_ListNop MatPlus [e11; e21]) (mk_ListNop
            MatPlus [e12;e22])
    | _ -> assert false
    

let rec combine_concats_aux c cs =
    match cs with
    | [] -> (c, [])
    | c' :: cs' -> if is_concatpair c c' then
        let c'' = combine_concatpair c c' in
        combine_concats_aux c'' cs'
    else
        let (a,b) = combine_concats_aux c cs' in
        (a, c' :: b)

let rec combine_concats cs =
    match cs with
    | [] -> []
    | c :: cs -> 
            let (c', cs') = combine_concats_aux c cs in
            c' :: (combine_concats cs')

let is_plus e = match e.e_node with Nary(ListNop MatPlus, _) -> true | _ -> false

let extract_plus e = match e.e_node with 
    | Nary(ListNop MatPlus, es) -> es
    | _ -> assert false


let rec norm_list_expr nftop  e =
    let nf = norm_list_expr nftop in 
    let ans = (match e.e_node with
    | App(op,es) when is_list_op op -> rewrite_list_op op (List.map nf es) 
    | Nary(nop, es) when is_list_nop nop -> rewrite_list_nop nop (List.map nf es)  
    | _ -> nftop e) in
    if (equal_expr ans e) then
        ans
    else
        nf ans
    


and rewrite_list_op op es  =
    match op, es with
    | ListOp MatMult, [e1;e2] -> rewrite_mult e1 e2   
    | ListOp MatOpp, [e1] -> rewrite_opp e1   
    | ListOp MatTrans, [e1] -> rewrite_trans e1   
    | ListOp MatConcat, [e1;e2] -> rewrite_concat e1 e2   
    | ListOp MatSplitLeft, [e1] -> rewrite_splitleft e1   
    | ListOp MatSplitRight, [e1] -> rewrite_splitright e1   
    | _, _ -> assert false 


and rewrite_list_nop nop es    =
    match nop with
    | ListNop MatPlus -> rewrite_plus es   
    | _ -> assert false

(* Normalization of operators: *)

(* (-a) * b -> - (a*b)
 * a * (-b) -> - (a*b)
 * - - a -> a
 * tr (-a) -> - (tr a)
*)

(* Normalize a*b:
    * (-a) * b -> - (a*b) *)

and rewrite_mult e e'   =
    match e.e_node, e'.e_node with
    (* e * (e1 * e2) -> (e * e1) * e2 *)
    | _, App(ListOp MatMult, [e1;e2]) -> (mk_ListMatMult (mk_ListMatMult
    e e1) e2)
    (* I * e' -> e' *)
    | Cnst(ListOf MatId), _ -> e'
    (* e * I -> e *)
    | _, Cnst(ListOf MatId) -> e
    (* 0 * e = e * 0 = 0 *)
    | Cnst(ListOf MatZero), _ | _, Cnst(ListOf MatZero) -> 
            let ((a,_),(_,d)) = (get_mat_mdims e.e_ty, get_mat_mdims e'.e_ty) in
            let (ln, _) = get_list_ty e.e_ty in
            mk_ListOfMatZero ln a d
    (* -e * -e' -> e * e'
     * -e * e' = e * -e' = - (e * e') *)
    | App(ListOp MatOpp,[e1]), App(ListOp MatOpp,[e'1]) -> (mk_ListMatMult
    e1 e'1)
    | App(ListOp MatOpp,[e1]), _ -> (mk_ListMatOpp (mk_ListMatMult e1 e'))
    | _, App(ListOp MatOpp, [e'1]) -> (mk_ListMatOpp (mk_ListMatMult e e'1))
    (* e * e'1||e'2 -> e*e'1 || e*e'2 *)
    | _, App(ListOp MatConcat, [e'1;e'2]) -> (mk_ListMatConcat  (mk_ListMatMult
    e e'1) (mk_ListMatMult e e'2))
    (* (a+b) * c -> a * c + b * c *)
    | Nary(ListNop MatPlus, es), _ -> (mk_ListNop MatPlus (
        List.map (fun x -> (mk_ListMatMult x e')) es))
    (* a * (b + c) -> a * b + a * c *)
    | _, Nary(ListNop MatPlus, e's) -> (mk_ListNop MatPlus (
        List.map (fun x' -> (mk_ListMatMult e x')) e's))
    | _, _ -> mk_ListMatMult  e  e' 


and rewrite_opp e    = 
    match e.e_node with
    (* --e -> e *)
    | App(ListOp MatOpp, [e']) -> e'
    (* -(a+b) -> -a + -b *)
    | Nary(ListNop MatPlus, es) -> (mk_ListNop MatPlus (List.map mk_ListMatOpp es))
    | _ -> mk_ListMatOpp e

    (* tr (a * b) -> (tr b) * (tr a) 
     * tr (a + b) -> tr a + tr b
     * tr (a - b) -> tr a - tr b
     * tr (-a) -> - (tr a) *)

and rewrite_trans e    =
    match e.e_node with
    (* tr (a * b) = tr b * tr a *)
    | App(ListOp MatMult, [a;b]) ->  (mk_ListMatMult  (mk_ListMatTrans  b )
    (mk_ListMatTrans a))
    (* tr (-a) -> - (tr a *)
    | App(ListOp MatOpp, [a]) ->  (mk_ListMatOpp (mk_ListMatTrans a))
    (* tr (a + b) -> tr a + tr b *)
    | Nary(ListNop MatPlus, es) ->  (mk_ListNop MatPlus (
                            List.map (fun x -> mk_ListMatTrans x) es))
    (* tr tr a = a *)
    | App(ListOp MatTrans, [a]) ->  a
    | _ -> mk_ListMatTrans e

and rewrite_plus es    = 

    (* if any subexpressions are additions, lift up *)
    let (subadds, others) = List.partition (is_plus) es in
    let subs = List.flatten (List.map extract_plus subadds) in
    let es = subs @ others in 
    (* remove zeroes *)
    let es = List.filter (fun x -> not (is_zero x)) es in
    (* remove opps *)
    let es' = remove_opps es in 

    (* combine concats: a || b + c || d -> (a+b) || (c+d) *)
    let es' = combine_concats es' in 

    let ans = (match (List.length es') with
    | 0 -> let (n,m) = get_mat_mdims (List.hd es).e_ty in let (a,_) =
        get_list_ty (List.hd es).e_ty in mk_ListOfMatZero a n m
    | _ -> mk_ListNop MatPlus es') in
    ans




and rewrite_concat e1 e2   = 
    match e1.e_node, e2.e_node with
    (* (sl a + b + c) || (sr a + d + e) -> a + (b + c) || (d + e) *) 
    | Nary(ListNop MatPlus, e1s), Nary(ListNop MatPlus, e2s) ->
        (* find all splitpairs between e1 and e2,
        extract them *)
        let t1 = (List.hd e1s).e_ty in
        let t2 = (List.hd e2s).e_ty in
        let (pairs, es1, es2) = rem_splitpairs e1s e2s in
        
        (match pairs with
        | [] -> mk_ListMatConcat e1  e2
        | _ ->
         (mk_ListNop MatPlus (pairs @ [
             mk_ListOp MatConcat [(mk_ListMatPlus_safe es1 t1); (mk_ListMatPlus_safe es2
             t2)]])))
    (* (sl a || sr a) -> a *)
    | App(ListOp MatSplitLeft, [a]), App(ListOp MatSplitRight, [b]) ->
        if a=b then a
        else mk_ListMatConcat e1 e2
    (* 0 || 0 -> 0 *)
    | Cnst(ListOf MatZero), Cnst(ListOf MatZero) ->
        let ((n,m),(_,m')) = (get_mat_mdims e1.e_ty, get_mat_mdims e2.e_ty) in
        let (a,_) = get_list_ty e1.e_ty in
        mk_ListOfMatZero a n (Type.MDPlus (m,m'))
    (* -a || -b -> - (a || b) *)
    | App(ListOp MatOpp,[a]), App(ListOp MatOpp, [b]) ->
            (mk_ListMatOpp (mk_ListMatConcat a b))
    | _ -> mk_ListMatConcat e1 e2

and rewrite_split wh e   =
    let sp_f = if wh then mk_ListMatSplitRight else mk_ListMatSplitLeft in
    match e.e_node with
    (* split (-a) -> - (sp a) *)
    | App(ListOp MatOpp, [a]) -> mk_ListMatOpp (sp_f a)
    (* sp (a + b) -> sp a + sp b *)
    | Nary(ListNop MatPlus,es) -> (mk_ListNop MatPlus (List.map sp_f  es))
    (* sp (a || b) -> (a or b) *)
    | App(ListOp MatConcat,[a;b]) -> if wh then b else a
    (* sp (a * b) -> a * (sp b) *)
    | App(ListOp MatMult, [a;b]) -> (mk_ListMatMult a (sp_f b))
    | _ -> sp_f e

and rewrite_splitleft e   = rewrite_split false e   

and rewrite_splitright  e   = rewrite_split true e   

let rec intersect_plus acc es1 es2 = match es1 with
    | [] -> (acc, [], es2)
    | e1 :: es1 -> if List.mem e1 es2 then 
        intersect_plus (e1::acc) es1 (rem_first_eq e1 es2)
    else let (acc', es1', es2') = intersect_plus acc es1 es2 in
    (acc', e1 :: es1', es2')

let mk_pl_safe es ty = match es with
| [] -> let (n,m) = get_mat_mdims ty in let (a,_) = get_list_ty ty in mk_ListOfMatZero a n m
| [e] -> e
| es -> mk_ListNop MatPlus es

let norm_list_ifte nfo b e1 e2 = (* turn b?e1:e2 into es + b?e1':e2', if e2 and e2 are
plusses and share things with es *)
    let nf = norm_list_expr nfo in

    print_string "hi";
    let ty = e1.e_ty in
    let es1 = if is_plus e1 then extract_plus e1 else [e1] in
    let es2 = if is_plus e2 then extract_plus e2 else [e2] in
    let (intersect, es1', es2') = intersect_plus [] es1 es2 in
    let e1' = mk_pl_safe es1' ty in
    let e2' = mk_pl_safe es2' ty in
    if (List.length intersect = 0) then 
        mk_Ifte b e1 e2
    else
        nf (mk_ListNop MatPlus (intersect @ [mk_Ifte b e1'
e2']))










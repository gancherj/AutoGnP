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

let is_zero e = match e.e_node with Cnst(MatZero) -> true | _ -> false

let is_opp_sym e e' = (e = (mk_MatOpp e')) || ((mk_MatOpp e) = e')

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



let is_splitleft e = match e.e_node with App(MatSplitLeft, _) -> true | _ -> false

let extract_splitleft e = match e.e_node with 
    | App(MatSplitLeft, [e]) -> e 
    | _ -> assert false

let is_splitright e = match e.e_node with App(MatSplitRight, _) -> true | _ -> false

let extract_splitright e = match e.e_node with 
    | App(MatSplitRight, [e]) -> e 
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
    | App(MatConcat, [e11;e12]), App(MatConcat, [e21;e22]) ->
    let ((n11,m11), (n12,m12),(n21,m21),(n22,m22)) = (ensure_mat_ty e11.e_ty,
    ensure_mat_ty e12.e_ty, ensure_mat_ty e21.e_ty, ensure_mat_ty e22.e_ty) in
    mdim_equal n11 n21 && mdim_equal m11 m21 && mdim_equal n12 n22 && mdim_equal
    m12 m22
    | _ -> false

let combine_concatpair e1 e2 =
    match e1.e_node, e2.e_node with
    | App(MatConcat, [e11;e12]), App(MatConcat, [e21;e22]) ->
            mk_MatConcat (mk_MatPlus [e11; e21]) (mk_MatPlus [e12;e22])
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

let is_plus e = match e.e_node with Nary(MatPlus, _) -> true | _ -> false

let extract_plus e = match e.e_node with 
    | Nary(MatPlus, es) -> es
    | _ -> assert false


let rec norm_mat_expr nftop  e =
    let nf = norm_mat_expr nftop in 
    let ans = (match e.e_node with
    | App(op,es) when is_mat_op op -> rewrite_mat_op op (List.map nf es) 
    | Nary(nop, es) when is_mat_nop nop -> rewrite_mat_nop nop (List.map nf es)  
    | _ -> nftop e) in
    if (equal_expr ans e) then
        ans
    else
        nf ans
    


and rewrite_mat_op op es  =
    match op, es with
    | MatMult, [e1;e2] -> rewrite_mult e1 e2   
    | MatOpp, [e1] -> rewrite_opp e1   
    | MatTrans, [e1] -> rewrite_trans e1   
    | MatMinus, [e1;e2] -> rewrite_minus e1 e2   
    | MatConcat, [e1;e2] -> rewrite_concat e1 e2   
    | MatSplitLeft, [e1] -> rewrite_splitleft e1   
    | MatSplitRight, [e1] -> rewrite_splitright e1   
    | _, _ -> assert false 


and rewrite_mat_nop nop es    =
    match nop with
    | MatPlus -> rewrite_plus es   
    | _ -> assert false

(* Normalization of operators: *)

(* (-a) * b -> - (a*b)
 * a * (-b) -> - (a*b)
 * - - a -> a
 * tr (-a) -> - (tr a)
*)

(* Normalize a*b:
    * (-a) * b -> - (a*b) *)

and rewrite_mult  e e'   =
    match e.e_node, e'.e_node with
    (* e * (e1 * e2) -> (e * e1) * e2 *)
    | _, App(MatMult, [e1;e2]) -> (mk_MatMult (mk_MatMult e e1) e2)
    (* I * e' -> e' *)
    | Cnst(MatId), _ -> e'
    (* e * I -> e *)
    | _, Cnst(MatId) -> e
    (* 0 * e = e * 0 = 0 *)
    | Cnst(MatZero), _ | _, Cnst(MatZero) -> 
            let ((a,_),(_,d)) = (ensure_mat_ty e.e_ty, ensure_mat_ty e'.e_ty) in
            mk_MatZero a d
    (* -e * -e' -> e * e'
     * -e * e' = e * -e' = - (e * e') *)
    | App(MatOpp,[e1]), App(MatOpp,[e'1]) -> (mk_MatMult e1 e'1)
    | App(MatOpp,[e1]), _ -> (mk_MatOpp (mk_MatMult e1 e'))
    | _, App(MatOpp, [e'1]) -> (mk_MatOpp (mk_MatMult e e'1))
    (* e * e'1||e'2 -> e*e'1 || e*e'2 *)
    | _, App(MatConcat, [e'1;e'2]) -> (mk_MatConcat (mk_MatMult e e'1)
    (mk_MatMult e e'2))
    (* (a+b) * c -> a * c + b * c *)
    | Nary(MatPlus, es), _ -> (mk_MatPlus (
                                List.map (fun x -> (mk_MatMult x e')) es))
    (* a * (b + c) -> a * b + a * c *)
    | _, Nary(MatPlus, e's) -> (mk_MatPlus (
                                List.map (fun x' -> (mk_MatMult e x')) e's))
    | _, _ -> mk_MatMult e e'


and rewrite_opp e    = 
    match e.e_node with
    (* --e -> e *)
    | App(MatOpp, [e']) -> e'
    (* -(a+b) -> -a + -b *)
    | Nary(MatPlus, es) -> (mk_MatPlus (List.map mk_MatOpp es))
    | _ -> mk_MatOpp e

    (* tr (a * b) -> (tr b) * (tr a) 
     * tr (a + b) -> tr a + tr b
     * tr (a - b) -> tr a - tr b
     * tr (-a) -> - (tr a) *)

and rewrite_trans e    =
    match e.e_node with
    (* tr (a * b) = tr b * tr a *)
    | App(MatMult, [a;b]) ->  (mk_MatMult (mk_MatTrans b) (mk_MatTrans a))
    (* tr (a - b) = tr a - tr b *)
    | App(MatMinus, [a;b]) ->  (mk_MatMinus (mk_MatTrans a) (mk_MatTrans b))
    (* tr (-a) -> - (tr a *)
    | App(MatOpp, [a]) ->  (mk_MatOpp (mk_MatTrans a))
    (* tr (a + b) -> tr a + tr b *)
    | Nary(MatPlus, es) ->  (mk_MatPlus (
                            List.map (fun x -> mk_MatTrans x) es))
    (* tr tr a = a *)
    | App(MatTrans, [a]) ->  a
    | _ -> mk_MatTrans e

and rewrite_plus  es    = 

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
    | 0 -> let (n,m) = ensure_mat_ty (List.hd es).e_ty in mk_MatZero n m
    | _ -> mk_MatPlus es') in
    ans

and rewrite_minus e1 e2    =
    (* a - b -> a + (-b) *)
    (mk_MatPlus [e1; mk_MatOpp e2])



and rewrite_concat  e1 e2   = 
    match e1.e_node, e2.e_node with
    (* (sl a + b + c) || (sr a + d + e) -> a + (b + c) || (d + e) *) 
    | Nary(MatPlus, e1s), Nary(MatPlus, e2s) ->
        (* find all splitpairs between e1 and e2,
        extract them *)
        let t1 = (List.hd e1s).e_ty in
        let t2 = (List.hd e2s).e_ty in
        let (pairs, es1, es2) = rem_splitpairs e1s e2s in
        
        (match pairs with
        | [] -> mk_MatConcat e1 e2
        | _ ->
         (mk_MatPlus (pairs @ [
            mk_MatConcat (mk_MatPlus_safe es1 t1) (mk_MatPlus_safe es2 t2)])))
    (* (sl a || sr a) -> a *)
    | App(MatSplitLeft, [a]), App(MatSplitRight, [b]) ->
        if a=b then a
        else mk_MatConcat e1 e2
    (* 0 || 0 -> 0 *)
    | Cnst(MatZero), Cnst(MatZero) ->
        let ((n,m),(_,m')) = (ensure_mat_ty e1.e_ty, ensure_mat_ty e2.e_ty) in
        mk_MatZero n (Type.MDPlus (m,m'))
    (* -a || -b -> - (a || b) *)
    | App(MatOpp,[a]), App(MatOpp, [b]) ->
            (mk_MatOpp (mk_MatConcat a b))
    | _ -> mk_MatConcat e1 e2

and rewrite_split wh e   =
    let sp_f = if wh then mk_MatSplitRight else mk_MatSplitLeft in
    match e.e_node with
    (* split (-a) -> - (sp a) *)
    | App(MatOpp, [a]) -> mk_MatOpp (sp_f a)
    (* sp (a + b) -> sp a + sp b *)
    | Nary(MatPlus,es) -> (mk_MatPlus (List.map sp_f es))
    (* sp (a || b) -> (a or b) *)
    | App(MatConcat,[a;b]) -> if wh then b else a
    (* sp (a * b) -> a * (sp b) *)
    | App(MatMult, [a;b]) -> (mk_MatMult a (sp_f b))
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
| [] -> let (n,m) = ensure_mat_ty ty in mk_MatZero n m
| [e] -> e
| es -> mk_MatPlus es

let norm_ifte nfo b e1 e2 = (* turn b?e1:e2 into es + b?e1':e2', if e2 and e2 are
plusses and share things with es *)
    let nf = norm_mat_expr nfo in

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
        nf (mk_MatPlus (intersect @ [mk_Ifte b e1'
e2']))

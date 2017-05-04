(* todo refactor *)
open Expr
open ExprUtils
open Util

let mk_log level = mk_logger "Deduce.Deduc" level "Deduc.ml"
let log_i = mk_log Bolt.Level.INFO

let rec rem_first_occ f xs = match xs with
| [] -> []
| x :: xs -> if (f x) then xs else x :: (rem_first_occ f xs)

let rec rem_first_eq e xs = match xs with
| [] -> []
| x :: xs -> if (x = e) then xs else x :: (rem_first_eq e xs)

(* find instances of e and -e in es, and remove the pair if found *)

let is_zero e = match e.e_node with Cnst(MatZero) -> true | _ -> false

let is_id e = match e.e_node with Cnst(MatId) -> true | _ -> false

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


let is_opp e = match e.e_node with App(MatOpp, _) -> true | _ -> false

let extract_opp e = match e.e_node with 
    | App(MatOpp, [e]) -> e 
    | _ -> assert false

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

let is_concat e = match e.e_node with App(MatConcat, _) -> true | _ -> false

let extract_concat e = match e.e_node with
    | App(MatConcat, [e1;e2]) -> (e1,e2)
    | _ -> assert false

let is_plus e = match e.e_node with Nary(MatPlus, _) -> true | _ -> false

let extract_plus e = match e.e_node with 
    | Nary(MatPlus, es) -> es
    | _ -> assert false

let is_minus e = match e.e_node with App(MatMinus, _) -> true | _ -> false

let extract_minus e = match e.e_node with
    | App(MatMinus, [e1;e2]) -> (e1, e2)
    | _ -> assert false

let is_mult e = match e.e_node with App(MatMult, _) -> true | _ -> false

let extract_mult e = match e.e_node with
    | App(MatMult, [e1;e2]) -> (e1, e2)
    | _ -> assert false

let is_tr e = match e.e_node with App(MatTrans, _) -> true | _ -> false

let extract_tr e = match e.e_node with
    | App(MatTrans, [e]) -> e
    | _ -> assert false


let rec norm_mat_expr nf e = 
    let ans = (match e.e_node with
    | App(op,es) -> norm_mat_op nf e op es
    | Nary(nop, es) -> norm_mat_nop nf e nop es
    | _ -> nf e) in
    ans

and norm_mat_op nf e op es =
    match op, es with
    | MatMult, [e1;e2] -> norm_mult nf e1 e2
    | MatOpp, [e1] -> norm_opp nf e1
    | MatTrans, [e1] -> norm_trans nf e1
    | MatMinus, [e1;e2] -> norm_minus nf e1 e2
    | MatConcat, [e1;e2] -> norm_concat nf e1 e2
    | MatSplitLeft, [e1] -> norm_splitleft nf e1
    | MatSplitRight, [e1] -> norm_splitright nf e1
    (*| FunCall(f), _ -> e
    | Ifte, [e1; e2; e3] -> mk_Ifte e1 (norm_mat_expr nf e2) (
    nf e3) *)
    | _, _ -> nf e


and norm_mat_nop nf e nop es =
    match nop with
    | MatPlus -> norm_plus nf es
    | _ -> nf e 

(* Normalization of operators: *)

(* (-a) * b -> - (a*b)
 * a * (-b) -> - (a*b)
 * - - a -> a
 * tr (-a) -> - (tr a)
*)

(* Normalize a*b:
    * (-a) * b -> - (a*b) *)

and norm_mult nfo e e' =
    let nf = norm_mat_expr nfo in
    let (e,e') = (nf e, nf e') in
    match (is_id e, is_id e') with
    | true, _ -> e'
    | _, true -> e
    | _ ->
    if (is_zero e) || (is_zero e') then
        let (a,_) = ensure_mat_ty e.e_ty in let (_,d) = ensure_mat_ty e'.e_ty in
        mk_MatZero a d
    else

    let o1 = is_opp e in
    let o2 = is_opp e' in

    match o1,o2 with (* move opp up mult *)
    | true, true -> let (e,e') = (nf (extract_opp e), nf
    (extract_opp e')) in mk_MatMult e e'
    | false, true -> let (e,e') = (e, nf (extract_opp e')) in
    mk_MatOpp (mk_MatMult e e')
    | true, false -> let (e,e') = (nf (extract_opp e), e') in
    mk_MatOpp (mk_MatMult e e')
    | false, false -> 
            
    if is_concat e' then
        let (e'1,e'2) = extract_concat e' in
        nf (mk_MatConcat (mk_MatMult e e'1) (mk_MatMult e e'2))
    else

    mk_MatMult e e' 

    (* - - a -> a *)
and norm_opp nfo e = 
    let nf = norm_mat_expr nfo in
    let e = nf e in
    let e = if is_opp e then begin 
        nf (extract_opp e)
        end
        else e 
    in
    if is_plus e then let es = extract_plus e in
        mk_MatPlus (List.map mk_MatOpp es)
    else
        mk_MatOpp e

    (* tr (a * b) -> (tr b) * (tr a) 
     * tr (a + b) -> tr a + tr b
     * tr (a - b) -> tr a - tr b
     * tr (-a) -> - (tr a) *)

and norm_trans nfo e =
    let nf = norm_mat_expr nfo in
    let e = nf e in
    if is_mult e then
        let (a,b) = extract_mult e in
        let a = nf a in
        let b = nf b in
        nf (mk_MatMult (mk_MatTrans b) (mk_MatTrans a))
    else if is_minus e then
        let (a,b) = extract_minus e in
        let a = nf a in
        let b = nf b in
        nf (mk_MatMinus (mk_MatTrans a) (mk_MatTrans b))
    else if is_opp e then
        let a = extract_opp e in
        let a = nf a in
        nf (mk_MatOpp (mk_MatTrans a))
    else if is_plus e then
        let es = extract_plus e in
        let es = List.map (fun x -> nf x) es in
        let es = List.map (fun x -> mk_MatTrans x) es in
        nf (mk_MatPlus es)
    else if is_tr e then
        let e = extract_tr e in
        nf e
    else
        mk_MatTrans e

and norm_plus nfo es = 
    let nf = norm_mat_expr nfo in

    (* normalize each subterm *)
    let es = List.map (fun x -> nf x) es in

    (* if any subexpressions are additions, lift up *)
    let (subadds, others) = List.partition (is_plus) es in
    let subs = List.flatten (List.map extract_plus subadds) in
    let es = subs @ others in 
    let es = List.filter (fun x -> not (is_zero x)) es in (* remove zeroes *)
    let es' = remove_opps es in (* look for ops that cancel *)
    let ans = (match (List.length es') with
    | 0 -> let (n,m) = ensure_mat_ty (List.hd es).e_ty in mk_MatZero n m
    | _ -> mk_MatPlus es') in
    ans

and norm_minus nfo e1 e2 =
    let nf = norm_mat_expr nfo in
    let e1 = nf e1 in
    let e2 = nf e2 in
    nf (mk_MatPlus [e1; mk_MatOpp e2])



and norm_concat nfo e1 e2 = 
    let nf = norm_mat_expr nfo in
    let e1 = nf e1 in
    let e2 = nf e2 in
    if is_plus e1 && is_plus e2 then  (* plus *)
        (* find all splitpairs between e1 and e2,
        extract them *)
        let t1 = (List.hd (extract_plus e1)).e_ty in
        let t2 = (List.hd (extract_plus e2)).e_ty in
        let es1 = List.map (nf) (extract_plus e1) in
        let es2 = List.map (nf) (extract_plus e2) in
        let (pairs, es1, es2) = rem_splitpairs es1 es2 in
        nf (mk_MatPlus (pairs @ [
            mk_MatConcat (mk_MatPlus_safe es1 t1) (mk_MatPlus_safe es2 t2)]))
    else if is_splitleft e1 && is_splitright e2 then (* sl x || sr x = x *)
        if is_splitpair e1 e2 then nf (extract_splitleft e1)
        else mk_MatConcat e1 e2
    else if is_zero e1 && is_zero e2 then (* 0 || 0 = 0, of correct dim *)
        let (n,m) = ensure_mat_ty e1.e_ty in
        let (_,m')= ensure_mat_ty e2.e_ty in
        mk_MatZero n (Type.MDPlus(m,m'))
    else if is_opp e1 && is_opp e2 then (* -a || -b = - (a || b) *)
        nf (mk_MatOpp (mk_MatConcat (extract_opp e1)
        (extract_opp e2)))
    else
        mk_MatConcat e1 e2

and norm_split nfo wh e =
    let sp_f = if wh then mk_MatSplitRight else mk_MatSplitLeft in
    let nf = norm_mat_expr nfo in
    let e = nf e in
    if is_opp e then
        mk_MatOpp (sp_f (extract_opp e))
    else if is_plus e then (* sl (a + b) -> sl a + sl b *)
        let es = List.map (nf) (extract_plus e) in
        let es = List.map (sp_f) es in
        nf (mk_MatPlus es)
    else if is_concat e then
        let (e1,e2) = extract_concat e in
        if wh then nf e2 else nf e1
    else if is_mult e then
        let (e1,e2) = extract_mult e in
        nf (mk_MatMult e1 (sp_f e2))
    else
        sp_f e 

and norm_splitleft nf e = norm_split nf false e

and norm_splitright nf e = norm_split nf true e

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

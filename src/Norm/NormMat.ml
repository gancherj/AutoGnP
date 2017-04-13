open Expr

(* find instances of e and -e in es, and remove the pair if found *)

let is_zero e = match e.e_node with Cnst(MatZero) -> true | _ -> false

let is_opp_sym e e' = (e = (mk_MatOpp e')) || ((mk_MatOpp e) = e')

let contains_op e es = List.exists (fun x -> is_opp_sym e x) es

let rec rem_first_op x es = match es with
    | [] -> []
    | e :: es' -> if is_opp_sym x e then es' else rem_first_op x es'

let rem_step so_far e = 
    if contains_op e so_far then 
        let es = rem_first_op e so_far in
        es
    else
        e :: so_far

let remove_opps es =
    List.fold_left rem_step [] es

let is_opp e = match e.e_node with App(MatOpp, _) -> true | _ -> false

let extract_opp e = match e.e_node with 
    | App(MatOpp, [e]) -> e 
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


let rec norm_mat_expr ~strong e = 
    match e.e_node with
    | App(op,es) -> norm_mat_op ~strong op es
    | Nary(nop, es) -> norm_mat_nop ~strong nop es
    | _ -> e

and norm_mat_op ~strong op es =
    match op, es with
    | MatMult, [e1;e2] -> norm_mult ~strong e1 e2
    | MatOpp, [e1] -> norm_opp ~strong e1
    | MatTrans, [e1] -> norm_trans ~strong e1
    | MatMinus, [e1;e2] -> norm_minus ~strong e1 e2
    | _, _ -> assert false

and norm_mat_nop ~strong nop es =
    match nop with
    | MatPlus -> norm_plus ~strong es
    | _ -> assert false

(* Normalization of operators: *)

(* (-a) * b -> - (a*b)
 * a * (-b) -> - (a*b)
 * - - a -> a
 * tr (-a) -> - (tr a)
*)

(* Normalize a*b:
    * (-a) * b -> - (a*b) *)

and norm_mult ~strong e e' =
    let (e,e') = (norm_mat_expr ~strong e, norm_mat_expr ~strong e') in
    if (is_zero e) || (is_zero e') then
        let (a,_) = ensure_mat_ty e.e_ty in let (_,d) = ensure_mat_ty e'.e_ty in
        mk_MatZero a d
    else

    let (e, e') = match (is_opp e), (is_opp e') with (* move opp up mult *)
    | true, true -> (norm_mat_expr ~strong (extract_opp e), norm_mat_expr
    ~strong (extract_opp e'))
    | false, true -> (e, norm_mat_expr ~strong (extract_opp e'))
    | true, false -> (norm_mat_expr ~strong (extract_opp e), e')
    | false, false -> (e, e') in
  
    mk_MatMult e e'

    (* - - a -> a *)
and norm_opp ~strong e = 
    let e = if is_opp e then begin 
        norm_mat_expr ~strong (extract_opp e)
        end
        else e 
    in

    mk_MatOpp e

    (* tr (a * b) -> (tr b) * (tr a) 
     * tr (a + b) -> tr a + tr b
     * tr (a - b) -> tr a - tr b
     * tr (-a) -> - (tr a) *)

and norm_trans ~strong e =
    if is_mult e then
        let (a,b) = extract_mult e in
        let a = norm_mat_expr ~strong a in
        let b = norm_mat_expr ~strong b in
        norm_mat_expr ~strong (mk_MatMult (mk_MatTrans b) (mk_MatTrans a))
    else if is_minus e then
        let (a,b) = extract_minus e in
        let a = norm_mat_expr ~strong a in
        let b = norm_mat_expr ~strong b in
        norm_mat_expr ~strong (mk_MatMinus (mk_MatTrans a) (mk_MatTrans b))
    else if is_opp e then
        let a = extract_opp e in
        let a = norm_mat_expr ~strong a in
        norm_mat_expr ~strong (mk_MatOpp (mk_MatTrans a))
    else if is_plus e then
        let es = extract_plus e in
        let es = List.map (fun x -> norm_mat_expr ~strong x) es in
        let es = List.map (fun x -> mk_MatTrans x) es in
        norm_mat_expr ~strong (mk_MatPlus es)
    else if is_tr e then
        let e = extract_tr e in
        norm_mat_expr ~strong e
    else
        mk_MatTrans e

and norm_plus ~strong es = 
    (* normalize each subterm *)
    let es = List.map (fun x -> norm_mat_expr ~strong x) es in

    (* if any subexpressions are additions, lift up *)
    let (subadds, others) = List.partition (is_plus) es in
    let subs = List.flatten (List.map extract_plus subadds) in
    let es = subs @ others in 
    let es = List.filter (fun x -> not (is_zero x)) es in (* remove zeroes *)
    let es' = remove_opps es in (* look for ops that cancel *)
    match (List.length es') with
    | 0 -> let (n,m) = ensure_mat_ty (List.hd es).e_ty in mk_MatZero n m
    | _ -> mk_MatPlus es'

and norm_minus ~strong e1 e2 =
    let e1 = norm_mat_expr ~strong e1 in
    let e2 = norm_mat_expr ~strong e2 in
    norm_mat_expr ~strong (mk_MatPlus [e1; mk_MatOpp e2])

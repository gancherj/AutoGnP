(* TODO: refactor; this is very ugly *)
open Expr
open ExprUtils
open Util

module L = List

let rec superset es = match es with
| [] -> [[]]
| e :: es -> let ps = superset es in
             ps @ List.map (fun ss -> e :: ss) ps

let complement ss es = List.filter (fun x -> not (List.mem x ss)) es

let viable_subsets es = let subsets = superset es in
let subsets = List.filter (fun ss -> not (List.length ss < 1 || List.length es - List.length
ss < 1)) subsets in
List.map (fun ss -> (ss, complement ss es)) subsets

let all_adds es = let subsets = viable_subsets es in
List.map (fun sc -> let (s,c) = sc in (mk_MatPlus s, mk_MatPlus c))
subsets




let mk_log level = mk_logger "Deduce.DeducMat" level "DeducMat.ml"
let log_i = mk_log Bolt.Level.DEBUG

let is_some o = match o with | Some _ -> true | None -> false
let extract_opt o = match o with | Some e -> e | None -> assert false

let is_app op e = match e.e_node with | App(op',_) when op'=op -> true | _ -> false

let is_mult e = match e.e_node with | App(MatMult,_) -> true | _ -> false


let unary_app_extract op e = match e.e_node with | App(op', [e']) when op'=op ->
    e' | _ -> 
    log_i (lazy (fsprintf "uhoh: expected op %a, got exp %a" pp_op (op,[e]) pp_expr
    e)); assert false

let binary_app_extract op e = match e.e_node with | App(op', [e1;e2]) when
op'=op -> (e1,e2) | _ ->
    log_i (lazy (fsprintf "uhoh")); assert false


let plus_unary_extract op es =  mk_MatPlus (List.map (unary_app_extract op) es)

let find_i ecs e =
    snd (List.find (fun x -> (fst x) = e) ecs)

let ei_op ei op = let (e,i) = ei in (op e, I (op (expr_of_inverter i)))

let mult_issplitl e = match e.e_node with
| App(MatMult, [e1;e2]) -> is_app MatSplitLeft e2
| _ -> false

let mult_issplitr e = match e.e_node with
| App(MatMult, [e1;e2]) -> is_app MatSplitRight e2
| _ -> false

let mult_extractsplitl e = match e.e_node with
| App(MatMult, [e1;e2]) -> (match e2.e_node with | App(MatSplitLeft, [e']) ->
        mk_MatMult e1 e' | _ -> assert false)
| _ -> assert false

let mult_extractsplitr e = match e.e_node with
| App(MatMult, [e1;e2]) -> (match e2.e_node with | App(MatSplitRight, [e']) ->
        mk_MatMult e1 e' | _ -> assert false)
| _ -> assert false


let rec mult_split_extr es = match es with
| [] -> []
| e :: es' -> (match (mult_issplitl e, mult_issplitr e) with
               | true, _ -> (mk_MatSplitLeft (mult_extractsplitl e)) ::
                   mult_split_extr es'
               | _, true -> (mk_MatSplitRight (mult_extractsplitr e)) ::
                   mult_split_extr es'
               | false, false -> e :: (mult_split_extr es'))


let plus_unary_fold es =
            let es = mult_split_extr es in
            if (List.for_all (is_app MatTrans) es) then
                Some (mk_MatTrans (plus_unary_extract MatTrans es)) else
            if (List.for_all (is_app MatOpp) es) then
                Some (mk_MatOpp (plus_unary_extract MatOpp es)) else
            if (List.for_all (is_app MatSplitLeft) es) then
                Some (mk_MatSplitLeft (plus_unary_extract MatSplitLeft es)) else
            if (List.for_all (is_app MatSplitRight) es) then
                Some (mk_MatSplitRight (plus_unary_extract MatSplitRight es)) else
            None
            

let extend_trans (ecs : (expr * inverter) list) =
    let ex_tr (ei : (expr * inverter)) = let (e,i) = ei in
        (mk_MatTrans e, I (mk_MatTrans (expr_of_inverter i))) in
    let ecst = List.map ex_tr ecs in
    ecs @ ecst


let rec extend_splits (ecs : (expr * inverter) list) = match ecs with
    | [] -> []
    | ei :: ecs -> 
        if (Type.is_Mat_splittable (fst ei).e_ty) then 
            let ei'1 = ei_op ei mk_MatSplitLeft in
            let ei'2 = ei_op ei mk_MatSplitRight in
            ei::ei'1::ei'2::(extend_splits ecs)
        else
            ei :: (extend_splits ecs)

let split_exists ecs e =
    if (Type.is_Mat_splittable e.e_ty) then
    let es = L.map fst ecs in
    if (List.mem (mk_MatSplitLeft e) es) && (List.mem (mk_MatSplitRight e) es)
    then true else false
    else
        false


let find_split (ecs : (expr * inverter) list) e =
    let eL = mk_MatSplitLeft e in
    let eR = mk_MatSplitRight e in
    I (mk_MatConcat (expr_of_inverter (find_i ecs eL)) (expr_of_inverter (find_i
    ecs eR)))
    
let norm_ecs ecs =
    let norm_ex ei = let (e,i) = ei in
        (Norm.norm_expr ~strong:true e, I (Norm.norm_expr ~strong:true (expr_of_inverter i))) in
    List.map norm_ex ecs

type matprog = | InProg | Ans of (inverter option)

let rec solve_mat' seen_already (ecs : (expr * inverter) list) (e : expr) =
    if Hashtbl.mem !seen_already e then 
        (match (Hashtbl.find !seen_already e) with
        | InProg -> Hashtbl.remove !seen_already e; None
        | Ans i -> i)
    else ( 
        (Hashtbl.add !seen_already e InProg);

    log_i (lazy (fsprintf "SOLVE MAT: trying to deduce %a" pp_expr e));



    (*let e = Norm.norm_expr_strong e in *)
    let es = L.map fst ecs in
    if (List.mem e es) then (* if e is in es, return corresponding i *)
        begin
        log_i (lazy (fsprintf "SOLVE MAT: found %a in list" pp_expr e));
        let ans = Some (find_i ecs e) in
        Hashtbl.add !seen_already e (Ans(ans));
        ans
        end 
    else
    if (split_exists ecs e) then
        let ans = Some (find_split ecs e) in
        Hashtbl.add !seen_already e (Ans(ans));
        ans
    else
        let ans = match e.e_node with
    | Nary(MatPlus, es) ->  (solve_plus seen_already ecs es)
    | App(MatMult, [e1;e2]) -> (solve_mult seen_already ecs e1 e2)
    | App(MatTrans, [e1]) -> (solve_trans seen_already ecs e1)
    | App(MatSplitLeft, [e]) -> solve_split seen_already mk_MatSplitLeft ecs e
    | App(MatSplitRight, [e]) -> solve_split seen_already mk_MatSplitRight ecs e
    | App(MatConcat, [e1;e2]) -> (solve_concat seen_already ecs e1 e2) (* todo
    *)
    | App(MatOpp, [e])       -> (solve_opp seen_already ecs e) (* todo *)
    | App(MatMinus, [e1;e2]) -> (solve_minus seen_already ecs e1 e2) (* todo *)

    | _ -> None
    
        in
        Hashtbl.add !seen_already e (Ans(ans));
        ans)

and solve_split seen spf ecs e =
    match (solve_mat' seen ecs e) with
    | Some a -> Some (I (spf (expr_of_inverter a)))
    | None -> None
    
and solve_opp seen ecs e =
    match (solve_mat' seen ecs e) with
    | Some a -> Some (I (mk_MatOpp (expr_of_inverter a)))
    | None -> None

and solve_minus seen ecs e1 e2 = solve_mat' seen ecs (mk_MatPlus [e1 ;(mk_MatOpp
e2)])

and solve_concat seen ecs e1 e2 =
    match (solve_mat' seen ecs e1, solve_mat' seen ecs e2) with
    | Some a1, Some a2 -> Some (I (mk_MatConcat (expr_of_inverter a1)
    (expr_of_inverter a2)))
    | _ -> None

and try_solve_all seen ecs es = match es with
| [] -> None
| e :: es -> let (e1, e2) = e in
        log_i (lazy (fsprintf "try_solve_all trying (%a,%a)" pp_expr e1 pp_expr
        e2));
        match (solve_mat' seen ecs e1, solve_mat' seen ecs e2) with | Some i1,
        Some i2 -> Some (I (mk_MatPlus [expr_of_inverter i1; expr_of_inverter
        i2])) | _, _->
        try_solve_all seen ecs es

and solve_plus seen ecs es = 
    if (List.length es = 1) then solve_mat' seen ecs (List.hd es) else 
    let ans = List.map (solve_mat' seen ecs) es in
    if (List.for_all is_some ans) then
        let is = List.map extract_opt ans in
        let ess = List.map expr_of_inverter is in
        Some (I (mk_MatPlus ess))
    else match (try_solve_all seen ecs (all_adds es)) with
    | Some i -> Some i
    | None ->
    match plus_unary_fold es with
    | Some e -> solve_mat' seen ecs e
    | None -> 
            None
           
and try_all seen ecs es = match es with
| [] -> None
| e :: es -> match (solve_mat' seen ecs e) with
             | Some i -> Some i
             | None -> try_all seen ecs es

and solve_mult seen ecs e1 e2 =
    let a1 = solve_mat' seen ecs e1 in (* try to solve e1 and e2 *)
    let a2 = solve_mat' seen ecs e2 in
    match a1, a2 with
    | Some i1, Some i2 ->
    let e1' = expr_of_inverter i1 in
    let e2' = expr_of_inverter i2 in
    Some (I (mk_MatMult e1' e2'))
    | _ -> 
    
    match e1.e_node, e2.e_node with
    | App(MatTrans, [e]), App(MatTrans, [e']) ->


    let to_try = [] in
    let to_try = 
        if (is_mult e2) then (* try left-reassociated version *)
        let (e21, e22) = binary_app_extract MatMult e2 in
        let enew = mk_MatMult (mk_MatMult e1 e21) e22 in
        enew :: to_try
        else to_try in

    let to_try =
    if (is_mult e1) then
        let (e11, e12) = binary_app_extract MatMult e1 in
        let enew = mk_MatMult e11 (mk_MatMult e12 e2) in
        enew :: to_try
    else to_try in

    try_all seen ecs to_try
    | _ -> None

and solve_trans seen ecs e1 =
    match (solve_mat' seen ecs e1) with
    | Some a -> 
    let e = expr_of_inverter a in
    Some (I (mk_MatTrans e))
    | None -> None

let solve_mat ecs e =
    (*let e = Norm.norm_expr ~strong:true e in*)
    (if (List.length ecs = 0)  then log_i (lazy (fsprintf "nothing given :("))
    else

    List.iter (fun ei -> 
        log_i (lazy (fsprintf "(%a,%a)" pp_expr (fst ei) pp_expr
        (expr_of_inverter (snd ei))))) ecs);
    let ecs = norm_ecs ecs in 
    let ecs = extend_splits ecs in
    let ecs = extend_trans ecs in
    let ecs = extend_splits ecs in
    let ecs = extend_trans ecs in
    let ecs = extend_splits ecs in
    
    let seen = ref (Hashtbl.create 100) in

    let a1 = solve_mat' seen ecs e in
    match a1 with
    | Some ans -> ans
    | None -> 
    let a2 = solve_mat' seen ecs (mk_MatTrans e) in
    match a2 with
    | Some ans -> ans
    | None ->
    log_i (lazy (fsprintf "SOLVE MAT: couldn't find %a" pp_expr e)); raise Not_found

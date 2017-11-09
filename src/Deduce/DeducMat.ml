open Expr
open ExprUtils
open Util

let is_some e = match e with
    | Some _ -> true
    | _ -> false

let rec get_somelist es = match es with
    | [] -> []
    | e :: es' ->
            match e with
            | Some a -> a :: (get_somelist es')
            | _ -> []

let mk_log level = mk_logger "Deduce.DeducMat" level "DeducMat.ml"
let log_i = mk_log Bolt.Level.INFO

let norm_e e = Norm.norm_expr ~strong:true e

let i_bop op i1 i2 = I (op (expr_of_inverter i1) (expr_of_inverter i2))
let i_mkapp o is ty = I (mk_App o (List.map expr_of_inverter is) ty) 

let can_split_ei ei = Type.split_compat (fst ei).e_ty
let matplus_bop e1 e2 = mk_MatPlus [e1;e2]

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

   


let try_find etbl e =
    try
        Some (He.find etbl e)
    with
    Not_found -> try
        Some (He.find etbl (norm_e e))
    with
        Not_found -> None

(* try to solve for every e in es. if not none, all succeeded *)
let rec try_all etbl es =
    let tries = List.map (solve etbl) es in
    if List.for_all is_some tries then
        Some (get_somelist tries)
    else None


(* try to solve any add in adds *)
and solve_adds etbl adds = match adds with
    | [] -> None
    | (e1, e2) :: adds' ->
            match (solve etbl e1, solve etbl e2) with
            | (Some i1, Some i2) -> (Some (i_bop matplus_bop i1 i2))
            | _ -> solve_adds etbl adds'


and solve etbl e =
    match e.e_node with
    | Nary(MatPlus, es') -> (* plus; decompose *)
            (match solve_adds etbl (all_adds es') with
            | Some i -> Some i
            | None -> try_find etbl e)
            
    | App(op, es') ->
            (match try_all etbl es' with
            | Some is -> Some (i_mkapp op is e.e_ty)
            | None -> try_find etbl e)

    | _ -> try_find etbl e

let rec try_solve_any etbl es = match es with
    | [] -> None
    | e::es' -> match solve etbl e with
        | Some i -> Some i
        | None -> try_solve_any etbl es'

let i_unnorm depth ei =
    let es = UnnormMat.expand (fst ei) depth in
    List.map (fun e -> (e, (snd ei))) es

let ecs_expand_unnorm ecs depth =
    List.flatten (List.map (i_unnorm depth) ecs)

let solve_mat ecs e =
    let ecs' = ecs_expand_unnorm ecs 6 in
    let etbl = He.create (List.length ecs') in
    List.iter (fun (e,i) -> He.add etbl e i) ecs';
    List.iter (fun (e,i) -> He.add etbl e i) (UnnormMat.add_unary 3 ecs);
    let es = UnnormMat.expand e 5 in
    match try_solve_any etbl es with
    | Some i -> i
    | None -> 
            log_i (lazy (fsprintf "not found: %a" pp_expr e));
            raise Not_found

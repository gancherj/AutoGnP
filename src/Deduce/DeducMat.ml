
open Expr
open ExprUtils
open Util
module L = List

let mk_log level = mk_logger "Deduce.DeducMat" level "DeducMat.ml"
let log_i = mk_log Bolt.Level.DEBUG

let direct_subterms o s es = 
  let go acc e =
    match e.e_node with
    | Nary(o',es') when o = o' ->
      Se.union acc (se_of_list es')
    | _ ->
      Se.add e acc
  in
  List.fold_left go s es

let find_i ecs e =
    snd (List.find (fun x -> (fst x) = e) ecs)

let rec solve_mat (ecs : (expr * inverter) list) (e : expr) =
    let es = L.map fst ecs in
    if (List.mem e es) then (* if e is in es, return corresponding i *)
        find_i ecs e
    else
    let e = Norm.norm_expr_strong e in
    match e.e_node with
    | Nary(MatPlus, es) -> solve_plus ecs es
    | _ -> log_i (lazy (fsprintf "couldn't find %a" pp_expr e)); raise Not_found

and solve_plus ecs es = 
    log_i (lazy (fsprintf "solving plus for %a, given:" pp_expr (mk_MatPlus es)));
    List.iter (fun ei -> log_i (lazy (fsprintf "(%a,%a)" pp_expr (fst ei)
    pp_expr (expr_of_inverter (snd ei))))) ecs;
    let is = List.map (solve_mat ecs) es in
    let ess = List.map expr_of_inverter is in
    log_i (lazy (fsprintf "deduced %a" pp_expr (mk_MatPlus ess)));
    I (mk_MatPlus ess)


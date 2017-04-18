
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


let extend_trans (ecs : (expr * inverter) list) =
    let ex_tr (ei : (expr * inverter)) = let (e,i) = ei in
        (mk_MatTrans e, I (mk_MatTrans (expr_of_inverter i))) in
    let ecst = List.map ex_tr ecs in
    ecs @ ecst

let norm_ecs ecs =
    let norm_ex ei = let (e,i) = ei in
        (Norm.norm_expr ~strong:true e, I (Norm.norm_expr ~strong:true (expr_of_inverter i))) in
    List.map norm_ex ecs

let rec solve_mat' (ecs : (expr * inverter) list) (e : expr) =
    
    log_i (lazy (fsprintf "SOLVE MAT: trying to deduce %a given:" pp_expr e));

    (if (List.length ecs = 0)  then log_i (lazy (fsprintf "nothing given :("))
    else

    List.iter (fun ei -> 
        log_i (lazy (fsprintf "(%a,%a)" pp_expr (fst ei) pp_expr
        (expr_of_inverter (snd ei))))) ecs);


    let e = Norm.norm_expr_strong e in
    let es = L.map fst ecs in
    if (List.mem e es) then (* if e is in es, return corresponding i *)
        begin
            log_i (lazy (fsprintf "SOLVE MAT FOND"));
        (find_i ecs e)
        end 
    else
    match e.e_node with
    | Nary(MatPlus, es) -> solve_plus ecs es
    | App(MatMult, [e1;e2]) -> solve_mult ecs e1 e2
    | App(MatTrans, [e1]) -> solve_trans ecs e1
    | _ -> log_i (lazy (fsprintf "SOLVE MAT: couldn't find %a" pp_expr e)); raise Not_found

and solve_plus ecs es = 
    let is = List.map (solve_mat' ecs) es in
    let ess = List.map expr_of_inverter is in
    I (mk_MatPlus ess)

and solve_mult ecs e1 e2 =
    let i1 = solve_mat' ecs e1 in
    let i2 = solve_mat' ecs e2 in
    let e1' = expr_of_inverter i1 in
    let e2' = expr_of_inverter i2 in
    I (mk_MatMult e1' e2')

and solve_trans ecs e1 =
    let e = expr_of_inverter (solve_mat' ecs e1) in
    I (mk_MatTrans e)

    
let solve_mat ecs e =
    let ecs = extend_trans ecs in
    let ecs = norm_ecs ecs in 
    solve_mat' ecs e
    (* TODO the rest *)

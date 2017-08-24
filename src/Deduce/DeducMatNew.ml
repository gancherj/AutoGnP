open Expr
open ExprUtils
open Util

(* TODO: stack overflows -- bug or i need to move to a heap *)

module S = Set.Make (
    struct 
        type t = (expr * inverter)
        let compare ei1 ei2 =
            compare (fst ei1) (fst ei2)
    end)

let is_some e = match e with
    | Some _ -> true
    | _ -> false

let rec get_somelist es = match es with
    | [] -> []
    | e :: es' ->
            match e with
            | Some a -> a :: (get_somelist es')
            | _ -> []

let rec e_depth e = match e.e_node with
    | App(_, es) -> 1 + List.fold_left max 0 (List.map e_depth es)
    | Nary(_, es) -> 1 + List.fold_left max 0 (List.map e_depth es)
    | _ -> 0


let mk_log level = mk_logger "Deduce.DeducMat" level "DeducMat.ml"
let log_i = mk_log Bolt.Level.DEBUG

let norm_e e = Norm.norm_expr ~strong:true e
let norm_ei ei = (Norm.norm_expr ~strong:true (fst ei), I (Norm.norm_expr
~strong:true (expr_of_inverter (snd ei))))

let ei_op op ei = let (e,i) = ei in (op e, I (op (expr_of_inverter i)))
let ei_bop op ei1 ei2 = let (e1, i1) = ei1 in
                        let (e2, i2) = ei2 in
                        (op e1 e2, I (op (expr_of_inverter i1) (expr_of_inverter
                        i2)))

let i_bop op i1 i2 = I (op (expr_of_inverter i1) (expr_of_inverter i2))
let i_mkapp o is ty = I (mk_App o (List.map expr_of_inverter is) ty) 

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

let trans_add ei = [ei_op mk_MatTrans ei]

let split_add ei =
    if Type.is_Mat_splittable (fst ei).e_ty then
        [ei_op mk_MatSplitRight ei; ei_op mk_MatSplitLeft ei]
    else []

let opp_add ei = [ei_op mk_MatOpp ei]

let mul_add ei1 ei2 =
    if Type.matmult_compat_ty (fst ei1).e_ty (fst ei2).e_ty then
        [ei_bop mk_MatMult ei1 ei2]
    else
        []

let concat_add ei1 ei2 =
    if Type.concat_compat_ty (fst ei1).e_ty (fst ei2).e_ty then
        [ei_bop mk_MatConcat ei1 ei2]
    else
        []


let plus_add ei1 ei2 =
    if Type.equal_ty (fst ei1).e_ty (fst ei2).e_ty then
        [ei_bop matplus_bop ei1 ei2]
    else
        []



let set_add s l =
    List.iter (fun i ->
        s := S.add i !s) l






let extend_iter eset elist_orig = 
    S.iter (fun ei1 ->
        set_add eset (trans_add ei1);
        set_add eset (split_add ei1);
        set_add eset (opp_add ei1);
        List.iter (fun ei2 ->
            set_add eset (mul_add ei1 ei2);
            set_add eset (concat_add ei1 ei2);
            set_add eset (plus_add ei1 ei2)) elist_orig) !eset
    

let rec extend eset elist_orig depth =
    if depth == 0 then eset
    else 
        (extend_iter eset elist_orig; extend eset elist_orig (depth - 1))


let try_find e eset =
    let elist = S.elements !eset in
    let elist_norm = List.map norm_ei elist in
    try
        let (_,i) = List.find (fun ei -> (fst ei) == (norm_e e)) elist in
        Some i
    with
    Not_found -> None


let rec try_all eset es =
    let tries = List.map (solve eset) es in
    if List.for_all is_some tries then
        Some (get_somelist tries)
    else None

and solve_adds eset adds = match adds with
    | [] -> None
    | (e1, e2) :: adds' ->
            match (solve eset e1, solve eset e2) with
            | (Some i1, Some i2) -> (Some (i_bop matplus_bop i1 i2))
            | _ -> solve_adds eset adds'

and solve eset e =
    match e.e_node with
    | Nary(_, es') -> (* plus; decompose *)
            (match solve_adds eset (all_adds es') with
            | Some i -> Some i
            | None -> try_find e eset )
            
    | App(op, es') ->
            (match try_find e eset with
            | Some i -> Some i
            | None ->
                    (match try_all eset es' with
                    | Some is -> Some (i_mkapp op is e.e_ty)
                    | None -> None))
    | _ -> try_find e eset




let solve_mat ecs e =
    log_i (lazy (fsprintf "call solve_mat:"));
    List.iter (fun ei ->
        log_i (lazy (fsprintf "(%a, %a)" pp_expr (fst ei) pp_expr
        (expr_of_inverter (snd ei))))) ecs;
    log_i (lazy (fsprintf "trying to find %a" pp_expr e)); 
    (*let ecs = List.filter (fun ei -> not (S.is_empty (S.inter (subterms (fst ei))
    (subterms e)))) ecs in
    if (List.length ecs == 0) then
        raise Not_found
else*)
    let eset = ref (S.of_list ecs) in
    let eset = extend eset ecs (e_depth e / 2 + 1) in
    match solve eset e with
    | Some i -> i
    | None -> 
            
            raise Not_found

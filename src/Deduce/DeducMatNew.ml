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

let matplus_bop e1 e2 = mk_MatPlus [e1;e2]

let setmap f s = S.of_list (List.map f (S.elements s))

let trans_add eset =
    eset := S.union !eset (setmap (fun ei -> ei_op mk_MatTrans ei) !eset) 

let splits_add eset =
    let lft = (setmap (fun ei ->
        if Type.is_Mat_splittable (fst ei).e_ty then
            ei_op mk_MatSplitLeft ei
        else
            ei) !eset) in
    let rght = (setmap (fun ei ->
        if Type.is_Mat_splittable (fst ei).e_ty then
            ei_op mk_MatSplitRight ei
        else
            ei) !eset) in
    eset := S.union !eset (S.union lft rght)
    
let opp_add eset =
    eset := S.union !eset (setmap (fun ei -> ei_op mk_MatOpp ei) !eset) 
   
        
let mul_add eset eset_orig =
    S.iter (fun (e1, i1) ->
        S.iter (fun (e2, i2) ->
            if Type.matmult_compat_ty e1.e_ty e2.e_ty then
                let ei' = ei_bop mk_MatMult (e1,i1) (e2, i2) in
                eset := S.add ei' !eset
            else ()) eset_orig) eset_orig

let concat_add eset eset_orig =
    S.iter (fun (e1, i1) ->
        S.iter (fun (e2, i2) ->
            if Type.concat_compat_ty e1.e_ty e2.e_ty then
                let ei' = ei_bop mk_MatConcat (e1,i1) (e2, i2) in
                eset := S.add ei' !eset
            else ()) eset_orig) eset_orig


let plus_add eset eset_orig =
    S.iter (fun (e1, i1) ->
        S.iter (fun (e2, i2) ->
            if Type.equal_ty e1.e_ty e2.e_ty then
                let ei' = ei_bop matplus_bop (e1,i1) (e2, i2) in
                eset := S.add ei' !eset
            else ()) eset_orig) eset_orig
   




let extend_iter eset eset_orig = 
    trans_add eset;
    opp_add eset;
    splits_add eset;
    mul_add eset eset_orig;
    concat_add eset eset_orig;
    plus_add eset eset_orig
    

let norm_eset eset =
    setmap norm_ei eset

let try_find e eset =
    let eset_norm = norm_eset !eset in
    let elist = S.elements eset_norm in
    try
        let (_,i) = List.find (fun ei -> (fst ei) == (norm_e e)) elist in
        Some i
    with
    Not_found -> None


let rec try_solve eset eset_orig e depth =
    if depth == 0 then raise Not_found
    else
        match try_find e eset with
        | Some i -> i
        | None -> extend_iter eset eset_orig; try_solve eset eset_orig e (depth - 1)


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
    let eset = S.of_list ecs in
    let eset_ref = ref eset in
    try_solve eset_ref eset e 5 

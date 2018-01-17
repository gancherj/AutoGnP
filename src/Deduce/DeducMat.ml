open Expr
open MatData
open ExprUtils
open Util
open NCGroebner
open MatSig
open MatData
open Num

module MatRules = MkMat (Mat)
module MatMon = MkMon (Mat)
module MatGasbi = MkGasbi (MatMon)

open MatMon

let mk_log level = mk_logger "Core.CoreRules" level "CoreRules.ml"
let log_i = mk_log Bolt.Level.INFO

let expr_to_id (e : expr) : int = e.e_tag
let pol_of_base (elt : Mat.elt) : MatMon.pol = 
    let e = Mat.expr_of_elt elt in
    [MatGasbi.mk_vmon (expr_to_id e) (MatMon.shape_of_expr e)]






let i_op (f : expr -> expr) (i : inverter) =
    match i with
    | I e -> I (f e)

let sl_mi (mi : (Mat.mat * inverter)) : Mat.mat * inverter =
    (Mat.MSplitLeft (fst mi), (i_op mk_MatSplitLeft (snd mi)))
    
let sr_mi (mi : (Mat.mat * inverter)) : Mat.mat * inverter =
    (Mat.MSplitRight (fst mi), (i_op mk_MatSplitRight (snd mi)))


let contains_splittable (mis : (Mat.mat * inverter) list) : bool =
    List.exists (fun (m,_) -> Mat.shape_splittable (Mat.shape_of_expr (Mat.expr_of_mat m))) mis

let mi_decomp_split_aux (mi : (Mat.mat * inverter)) : (Mat.mat * inverter) list =
    let mshape = Mat.shape_of_expr (Mat.expr_of_mat (fst mi)) in
    if Mat.shape_splittable mshape then
        [sl_mi mi; sr_mi mi]
    else
        [mi]

let rec mis_decomp_split (mis : (Mat.mat * inverter) list) : (Mat.mat * inverter) list =
    if contains_splittable mis then
        mis_decomp_split (List.concat (List.map mi_decomp_split_aux mis))
    else mis 

let mis_add_trans (mis : (Mat.mat * inverter) list) =
    mis @ (List.map (fun (m,i) -> (Mat.MTrans m, i_op mk_MatTrans i)) mis)

let mis_norm (mis : (Mat.mat * inverter) list) =
    mis @ (List.map (fun (m,i) -> (MatRules.norm_mat m, i)) mis)

let mi_of_ei (ei : expr * inverter) =
    ((MatRules.norm_mat (Mat.mat_of_expr (fst ei))), snd ei)

(* pol_of_mat : translate splitleft, splitright, trans as atomic *)
let rec pol_of_mat : Mat.mat -> MatMon.pol = function
    | Mat.MPlus (_, ms) -> List.concat (List.map pol_of_mat ms)
    | Mat.MOpp m -> MatGasbi.mpoly_cmul (Num.Int (-1)) (pol_of_mat m)
    | Mat.MMult (m1,m2) -> MatGasbi.mpoly_mul (pol_of_mat m1) (pol_of_mat m2)
    | Mat.MTrans m -> 
            pol_of_base (Mat.elt_of_expr (mk_MatTrans (Mat.expr_of_mat m)))
    | Mat.MConcat _ -> failwith "Translating concat!"
    | Mat.MSplitLeft m -> 
            pol_of_base (Mat.elt_of_expr (mk_MatSplitLeft (Mat.expr_of_mat m)))
    | Mat.MSplitRight m -> 
            pol_of_base (Mat.elt_of_expr (mk_MatSplitRight (Mat.expr_of_mat m)))
    | Mat.MId s -> failwith "identity matrix"
    | Mat.MZero s -> failwith "zero matrix"
    | Mat.MBase exp -> pol_of_base exp


let pi_of_mi (mi : Mat.mat * inverter) =
    (pol_of_mat (fst mi), snd mi)

type split_subgoals = SSBase of Mat.mat | SSConcat of (split_subgoals * split_subgoals)

let rec subgoals_of_targ (m : Mat.mat) =
    if Mat.shape_splittable (Mat.shape_of_expr (Mat.expr_of_mat m)) then
        let m_sl = Mat.MSplitLeft m in
        let m_sr = Mat.MSplitRight m in
        SSConcat (subgoals_of_targ m_sl, subgoals_of_targ m_sr)
    else
        SSBase m

let rec norm_subgoals : split_subgoals -> split_subgoals = function
    | SSBase m -> SSBase (MatRules.norm_mat m)
    | SSConcat (s1, s2) -> SSConcat (norm_subgoals s1, norm_subgoals s2)


(* --- actual deducibility --- *)

let inverter_of_pol (p : MatMon.pol)  (base : expr list) =
    let expr_of_mon (m : MatMon.mon) =
        let rec build_mult (is : int list) (s : MatMon.shape) : expr =
            match is with
            | i :: [] -> List.nth base ((-i) - 1)
            | (i1 :: i2 :: []) -> mk_MatMult (List.nth base ((-i1) - 1)) (List.nth base ((-i2) - 1))
            | i :: is' -> mk_MatMult (List.nth base ((-i) - 1)) (build_mult is' s)
            | [] -> failwith "bad monomial"
        in
        match m.MatMon.coeff with
        | Int 1 -> (build_mult (m.MatMon.vars) (m.MatMon.size))
        | _ -> failwith "bad coeff"
   in
   match p with
   | [] -> tacerror "empty p?"
   | _ ->
       I (mk_MatPlus (List.map (expr_of_mon) p))

let rec deduc_subgoals (sg : split_subgoals) (base : (MatMon.pol * inverter) list) =
    match sg with
    | SSConcat (sg1,sg2) ->
            (match (deduc_subgoals sg1 base, deduc_subgoals sg2 base) with
            | (I i1, I i2) -> I (mk_MatConcat i1 i2))
    | SSBase m ->
            let targ_pol = pol_of_mat m in
            let targ_invpol = MatGasbi.inverter targ_pol (List.map fst base) in
            inverter_of_pol targ_invpol (List.map expr_of_inverter (List.map snd base)) 

let solve_mat eis e = 
    (* compute target pol, split into subgoals *)
    let targ_m' = (Mat.mat_of_expr (Norm.norm_expr_strong e)) in
    let targ_sgs = norm_subgoals (subgoals_of_targ targ_m') in
    (* TODO deal with transpositions? *)
    
    (* compute input pols, fully split them *)
    let mis'' = List.map mi_of_ei eis in
    let mis = mis_add_trans (mis_decomp_split mis'') in
    let pis = List.map pi_of_mi (mis_norm mis) in
    (* TODO throw in transpositions? *)
    
    deduc_subgoals targ_sgs pis




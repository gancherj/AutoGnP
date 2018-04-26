open Expr
open MatData
open ExprUtils
open Util
open NCGroebner
open MatSig
open MatData
open Num
open Abbrevs

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

let tr_mi (mi : (Mat.mat * inverter)) : Mat.mat * inverter =
    (Mat.MTrans (fst mi), i_op mk_MatTrans (snd mi))


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

let contains_leftsplittable (mis : (Mat.mat * inverter) list) : bool =
    List.exists (fun (m,_) -> Mat.shape_leftsplittable (Mat.shape_of_expr (Mat.expr_of_mat m))) mis

let mi_decomp_leftsplit_aux (mi : (Mat.mat * inverter)) : (Mat.mat * inverter) list =
    let mshape = Mat.shape_of_expr (Mat.expr_of_mat (fst mi)) in
    if Mat.shape_leftsplittable mshape then
        [tr_mi (sl_mi (tr_mi mi)); tr_mi (sr_mi (tr_mi mi))]
    else
        [mi]

let rec mis_decomp_leftsplit (mis : (Mat.mat * inverter) list) : (Mat.mat * inverter) list =
    if contains_leftsplittable mis then
        mis_decomp_leftsplit (List.concat (List.map mi_decomp_leftsplit_aux mis))
    else mis 

let mis_add_trans (mis : (Mat.mat * inverter) list) =
    mis @ (List.map tr_mi mis)

let mi_of_ei (ei : expr * inverter) =
    ((MatRules.norm_mat (Mat.mat_of_expr (fst ei))), snd ei)

let norm_mis (mis : (Mat.mat * inverter) list) =
    List.map (fun mi -> ((MatRules.norm_mat (fst mi), snd mi))) mis

let ei_of_mi (mi : Mat.mat * inverter) =
    ((Mat.expr_of_mat (fst mi), snd mi))

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

type split_subgoals = SSBase of Mat.mat | SSConcatR of (split_subgoals *
split_subgoals) | SSConcatL of (split_subgoals * split_subgoals)

let rec subgoals_of_targ (m : Mat.mat) =
    let s = Mat.shape_of_expr (Mat.expr_of_mat m) in
    if Mat.shape_splittable s then
        let m_sl = Mat.MSplitLeft m in
        let m_sr = Mat.MSplitRight m in
        SSConcatR (subgoals_of_targ m_sl, subgoals_of_targ m_sr)
    else if Mat.shape_leftsplittable s then
        let m_lsl = Mat.MTrans (Mat.MSplitLeft (Mat.MTrans m)) in
        let m_lsr = Mat.MTrans (Mat.MSplitRight (Mat.MTrans m)) in
        SSConcatL (subgoals_of_targ m_lsl, subgoals_of_targ m_lsr)
    else
        SSBase m

let rec norm_subgoals : split_subgoals -> split_subgoals = function
    | SSBase m -> SSBase (Mat.mat_of_expr (Norm.norm_expr_strong (Mat.expr_of_mat m)))
    | SSConcatL (s1, s2) -> SSConcatL (norm_subgoals s1, norm_subgoals s2)
    | SSConcatR (s1, s2) -> SSConcatR (norm_subgoals s1, norm_subgoals s2)


let rec pp_subgoals (fmt : F.formatter) (sg : split_subgoals) =
    match sg with
    | SSBase m -> F.fprintf fmt "%a" pp_expr (Mat.expr_of_mat m)
    | SSConcatL (s1, s2) -> pp_subgoals fmt s1; F.fprintf fmt ", "; pp_subgoals fmt s2
    | SSConcatR (s1, s2) -> pp_subgoals fmt s1; F.fprintf fmt ", "; pp_subgoals fmt s2
    


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
        | Int (-1) -> mk_MatOpp (build_mult (m.MatMon.vars) (m.MatMon.size))
        | _ -> tacerror "unknown coeff type"
   in
   match p with
   | [] -> tacerror "empty p?"
   | _ ->
       I (mk_MatPlus (List.map (expr_of_mon) p))

let rec deduc_subgoals (sg : split_subgoals) (base : (MatMon.pol * inverter) list) =
    match sg with
    | SSConcatR (sg1,sg2) ->
            (match (deduc_subgoals sg1 base, deduc_subgoals sg2 base) with
            | (I i1, I i2) -> I (mk_MatConcat i1 i2))
    | SSConcatL (sg1,sg2) ->
            (match (deduc_subgoals sg1 base, deduc_subgoals sg2 base) with
            | (I i1, I i2) -> I (mk_MatTrans (mk_MatConcat (mk_MatTrans i1)
            (mk_MatTrans i2))))
    | SSBase m ->
            let targ_pol = pol_of_mat m in
            let targ_invpol = MatGasbi.inverter targ_pol (List.map fst base) in
            inverter_of_pol targ_invpol (List.map expr_of_inverter (List.map snd base)) 

let rec constant_pis (s : Mat.shape) : (MatMon.pol * inverter) list =
    List.map (fun ce -> let p = pol_of_base (Mat.elt_of_expr ce) in (p, I ce))
    (Mat.all_constants_of_shape s)


let solve_mat eis e = 
    (* compute target pol, split into subgoals *)
    let targ_m' = (Mat.mat_of_expr e) in
    let targ_sgs = norm_subgoals (subgoals_of_targ targ_m') in
    
    (* compute input pols *)
    let mis = List.map mi_of_ei eis in
    (* take transpose *)
    let mis = mis_add_trans mis in
    (* fully split *)
    let mis = mis_decomp_split mis in
    (* fully left split *)
    let mis = mis_decomp_leftsplit mis in
    (* take transpose *)
    let mis = mis_add_trans mis in
    (* norm *)
    let mis = norm_mis mis in


    let pis = List.map pi_of_mi mis in

    (* throw in constants *)
    let pis = pis @ constant_pis (Mat.shape_of_expr e) in
    
    try
        deduc_subgoals targ_sgs pis
    with
        Not_found ->
          log_i (lazy (fsprintf "Mat: from %a could not deduce subgoals %a"
          (pp_list "," pp_expr) (List.map fst (List.map ei_of_mi mis))
          pp_subgoals targ_sgs));
          raise Not_found
         



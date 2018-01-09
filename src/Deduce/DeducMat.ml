open Expr
open MatData
open ExprUtils
open Util
open NCGroebner

module MatMon = MkMon (Mat)
module MatGasbi = MkGasbi (MatMon)

let expr_to_id : expr -> int = failwith "unimp"
let pol_of_base : Mat.elt -> MatMon.pol = failwith "unimp"


let rec pol_of_mat : Mat.mat -> MatMon.pol = function
    | Mat.MPlus (_, ms) -> List.concat (List.map pol_of_mat ms)
    | Mat.MOpp m -> MatGasbi.mpoly_cmul (Num.Int (-1)) (pol_of_mat m)
    | Mat.MMult (m1,m2) -> MatGasbi.mpoly_mul (pol_of_mat m1) (pol_of_mat m2)
    | Mat.MTrans m -> failwith "Translating trans!"
    | Mat.MConcat _ -> failwith "Translating concat!"
    | Mat.MSplitLeft _ -> failwith "Translating split!"
    | Mat.MSplitRight _ -> failwith "Translating split!"
    | Mat.MId s -> failwith "identity matrix"
    | Mat.MZero s -> failwith "zero matrix"
    | Mat.MBase exp -> pol_of_base exp

    

let solve_mat eis e = failwith "todo"

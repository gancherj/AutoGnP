open MatSig
open Expr
open Type

module Mat : MATDATA = struct
    type elt = expr
    type shape = mdim * mdim
    type mat =
        | MPlus of mat list
        | MOpp of mat
        | MMult of mat * mat
        | MTrans of mat
        | MConcat of mat * mat
        | MSplitLeft of mat
        | MSplitRight of mat
        | MId of shape
        | MZero of shape
        | MBase of elt
    let mult_shape p1 p2 = (fst p1, snd p2)
    let concat_shape p1 p2 = (fst p1, Type.MDPlus (snd p1, snd p2))
    let sl_shape p = match p with | (p1, MDPlus (p2, _)) -> (p1, p2) | _ -> assert false
    let sr_shape p = match p with | (p1, MDPlus (_, p2)) -> (p1, p2) | _ ->
        assert false
    let trans_shape (a,b) = (b,a)
    let elt_eq a b = equal_expr a b
    let shape_eq p1 p2 = Type.mdim_equal (fst p1) (fst p2) && Type.mdim_equal (snd p1) (snd p2)
    let shape_of_elt e = Type.dim_of_mat e.e_ty
    let elt_of_expr e = e
    let rec mat_of_expr e =
        match e.e_node with
        | App(MatMult, [e1;e2]) -> MMult (mat_of_expr e1, mat_of_expr e2)
        | App(MatOpp, [e]) -> MOpp (mat_of_expr e)
        | App(MatTrans, [e]) -> MTrans (mat_of_expr e)
        | App(MatConcat, [e1;e2]) -> MConcat (mat_of_expr e1, mat_of_expr e2)
        | App(MatSplitLeft, [e]) -> MSplitLeft (mat_of_expr e)
        | App(MatSplitRight, [e]) -> MSplitRight (mat_of_expr e)
        | Nary(MatPlus, es) -> MPlus (List.map mat_of_expr es)
        | Cnst(MatZero) -> let p = Type.dim_of_mat (e.e_ty) in MZero p
        | Cnst(MatId) -> MId (Type.dim_of_mat (e.e_ty))
        | _ -> MBase e
    let rec expr_of_mat m =
        match m with
        | MPlus ms -> 
                mk_MatPlus (List.map expr_of_mat ms)
        | MOpp m -> mk_MatOpp (expr_of_mat m)
        | MMult (m1,m2) -> mk_MatMult (expr_of_mat m1) (expr_of_mat m2)
        | MTrans m -> mk_MatTrans (expr_of_mat m)
        | MConcat (m1,m2) -> mk_MatConcat (expr_of_mat m1) (expr_of_mat m2)
        | MSplitLeft m -> mk_MatSplitLeft (expr_of_mat m)
        | MSplitRight m -> mk_MatSplitRight (expr_of_mat m)
        | MZero p -> mk_MatZero (fst p) (snd p)
        | MId p -> mk_MatId (fst p) (snd p)
        | MBase e -> e
  end

module MatRules = MkMat(Mat)


let get_dim (e : Expr.expr) = Type.dim_of_mat (e.Expr.e_ty)



let rec norm_mat_expr nftop e = 
    let nf = norm_mat_expr nftop in
    let rewr x = Mat.expr_of_mat (MatRules.norm_mat (Mat.mat_of_expr x)) in
    let ans = (match e.e_node with
    | App(op,es) when ExprUtils.is_mat_op op -> rewr (Expr.mk_App op (List.map nf es) e.Expr.e_ty)
    | Nary(nop, es) when ExprUtils.is_mat_nop nop -> rewr (Expr.mk_Nary nop (List.map nf es))
    | _ -> nftop e) in
    if (Expr.equal_expr ans e) then
        ans
    else
        nf ans


let norm_ifte nfo e e1 e2 =
    (* need to do the pulling out add thing *)
    let nf = norm_mat_expr nfo in
    Expr.mk_Ifte (nf e) (nf e1) (nf e2) 

(*



*)

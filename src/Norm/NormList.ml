open MatSig
open Expr
open Type

module ListMat : MATDATA = struct
    type shape = mdim * mdim * mdim
    type elt = LBase of expr | LOf of mdim * expr
    type mat =
        | MPlus of shape * mat list
        | MOpp of mat
        | MMult of mat * mat
        | MTrans of mat
        | MConcat of mat * mat
        | MSplitLeft of mat
        | MSplitRight of mat
        | MId of shape
        | MZero of shape
        | MBase of elt

    let mult_shape (a,b,_) (_,_,f) = (a, b, f)
    let concat_shape (a,b,c) (_, _, d) = (a, b, MDPlus (c,d))
    let sl_shape (a,b,c) = match c with
        | MDPlus (e, _) -> (a,b,e)
        | _ -> assert false
    let sr_shape (a,b,c) = match c with
        | MDPlus (_, e) -> (a,b,e)
        | _ -> assert false
    let trans_shape (a,b,c) = (a,c,b)

    let elt_eq e1 e2 =
        match e1,e2 with
        | LBase a, LBase b -> equal_expr a b
        | LOf (a,b), LOf (c,d) -> mdim_equal a c && equal_expr b d
        | _, _ -> false

    let shape_eq (a,b,c) (d,e,f) =
        mdim_equal a d &&
        mdim_equal b e &&
        mdim_equal c f

    let shape_of_elt e =
        match e with
        | LBase e -> let (a,f) = get_list_ty e.e_ty in
                     let (b,c) = dim_of_mat f in
                     (a,b,c)
        | LOf (a,t) -> let (b,c) = dim_of_mat (t.e_ty) in (a,b,c)


    let rec mat_of_expr e =
        match e.e_node with
        | App(ListOp MatMult, [e1;e2]) -> MMult (mat_of_expr e1, mat_of_expr e2)
        | App(ListOp MatOpp, [e]) -> MOpp (mat_of_expr e)
        | App(ListOp MatTrans, [e]) -> MTrans (mat_of_expr e)
        | App(ListOp MatConcat, [e1;e2]) -> MConcat (mat_of_expr e1, mat_of_expr e2)
        | App(ListOp MatSplitLeft, [e]) -> MSplitLeft (mat_of_expr e)
        | App(ListOp MatSplitRight, [e]) -> MSplitRight (mat_of_expr e)
        | Nary(ListNop MatPlus, es) -> 
                let (a,f) = get_list_ty (List.hd es).e_ty in
                let (b,c) = dim_of_mat f in
                MPlus ((a,b,c), List.map mat_of_expr es)
        | App(ListOf, [e']) -> 
                (match e'.e_node with
                | Cnst (MatZero) -> let (a,f) = get_list_ty e.e_ty in
                                    let (b,c) = dim_of_mat f in MZero (a,b,c)
                | Cnst (MatId) ->
                    let (a,f) = get_list_ty e.e_ty in
                    let (b,c) = dim_of_mat f in MId (a,b,c)
                | _ -> 
                    let (a,_) = get_list_ty e.e_ty in    
                    MBase (LOf (a, e')))
        | _ -> MBase (LBase e)

    let rec expr_of_mat m = 
        match m with
        | MPlus (_,xs) -> mk_ListNop MatPlus (List.map expr_of_mat xs)
        | MOpp x -> mk_ListMatOpp (expr_of_mat x)
        | MMult (x,y) -> mk_ListMatMult (expr_of_mat x) (expr_of_mat y)
        | MTrans x -> mk_ListMatTrans (expr_of_mat x)
        | MConcat (x,y) -> mk_ListMatConcat (expr_of_mat x) (expr_of_mat y)
        | MSplitLeft x -> mk_ListMatSplitLeft (expr_of_mat x)
        | MSplitRight x -> mk_ListMatSplitRight (expr_of_mat x)
        | MId (a,b,c) -> mk_ListOf a (mk_MatId b c)
        | MZero (a,b,c) -> mk_ListOf a (mk_MatZero b c)
        | MBase (LOf (d,e)) -> mk_ListOf d e
        | MBase (LBase e) -> e

    (* [a + b] -> [a] + [b] *)
    (* [a * b] -> [a] * [b] *)
    let extra_rewr m =
        match m with
        | MBase (LOf (d, e)) ->
                (match e.e_node with
                | Nary(MatPlus, es) -> 
                        let (b,c) = dim_of_mat (List.hd es).e_ty in
                        MPlus ((d,b,c), List.map (fun x -> MBase (LOf (d, x))) es)
                | App(MatMult, [e1;e2]) ->
                        MMult (MBase (LOf (d, e1)), MBase (LOf (d, e2)))
                | _ -> m)
        | _ -> m

end

module MatRules = MkMat(ListMat)

let rec norm_list_expr nftop e = 
    let nf = norm_list_expr nftop in
    let rewr x = ListMat.expr_of_mat (MatRules.norm_mat (ListMat.mat_of_expr x)) in
    let ans = (match e.e_node with
    | App(op,es) when ExprUtils.is_list_op op -> rewr (Expr.mk_App op (List.map nf es) e.Expr.e_ty)
    | Nary(nop, es) when ExprUtils.is_list_nop nop -> rewr (Expr.mk_Nary nop (List.map nf es))
    | _ -> nftop e) in
    if (Expr.equal_expr ans e) then
        ans
    else
        nf ans


let norm_list_ifte nftop e e1 e2 = 
    let nf = norm_list_expr nftop in
    Expr.mk_Ifte (nf e) (nf e1) (nf e2)

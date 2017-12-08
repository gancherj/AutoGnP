open MatSig


let get_dim (e : Expr.expr) = Type.dim_of_mat (e.Expr.e_ty)


let rec norm_mat_expr nftop e = 
    let nf = norm_mat_expr nftop in
    let rewr x = mat_expr_of_matsig (norm_matsig Expr.equal_expr get_dim
    (matsig_of_mat_expr x)) in
    let ans = (match e.Expr.e_node with
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



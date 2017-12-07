open MatSig


let get_dim (e : Expr.expr) = Type.dim_of_mat (e.Expr.e_ty)


let norm_mat_expr nftop e = 
    mat_expr_of_matsig (norm_matsig nftop Expr.equal_expr get_dim (matsig_of_mat_expr e))

let norm_ifte nfo e e1 e2 =
    (* TODO do the pulling adds out thing *)
    let nf = norm_mat_expr nfo in
    Expr.mk_Ifte (nf e) (nf e1) (nf e2) 



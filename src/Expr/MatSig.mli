open Expr


module type MATDATA = sig
        type elt
        type shape
        val mult_shape : shape -> shape -> shape
        val concat_shape : shape -> shape -> shape
        val sl_shape : shape -> shape
        val sr_shape : shape -> shape
        val trans_shape : shape -> shape
        
        val elt_eq : elt -> elt -> bool
        val shape_eq : shape -> shape -> bool

        val shape_of_elt : elt -> shape


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
        

        val mat_of_expr : expr -> mat
        val expr_of_mat : mat -> expr

        val extra_rewr : mat -> mat
    end

module type MATRULES = functor (Data : MATDATA) -> sig
    val norm_mat: Data.mat -> Data.mat
end

module MkMat : MATRULES


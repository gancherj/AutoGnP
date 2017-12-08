open Expr

type 'a matsig =
    | MPlus of ('a matsig) list
    | MOpp of ('a matsig)
    | MMult of ('a matsig) * ('a matsig)
    | MTrans of 'a matsig
    | MConcat of ('a matsig) * ('a matsig)
    | MSplitLeft of 'a matsig
    | MSplitRight of 'a matsig
    | MId of (Type.mdim * Type.mdim)
    | MZero of (Type.mdim * Type.mdim)
    | MBase of 'a (* variables, uninterpreted functions, ... *)

val matsig_of_mat_expr : expr -> expr matsig
val mat_expr_of_matsig : expr matsig -> expr

val matsig_of_matlist_expr : expr -> expr matsig
val matlist_expr_of_matsig : expr matsig -> expr 

val matsig_rewrite_step : ('a -> 'a -> bool) -> ('a -> Type.mdim * Type.mdim) -> 'a matsig -> 'a matsig
val norm_matsig : ('a -> 'a -> bool) -> ('a -> Type.mdim * Type.mdim) -> 'a matsig -> 'a matsig

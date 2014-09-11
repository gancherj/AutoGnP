(*s fixme *)

open Expr
open CoreRules
open Syms

val t_norm : ?fail_eq:bool -> tactic

val t_norm_nounfold : tactic

val t_unfold_only : tactic 

val t_norm_unknown : expr list -> tactic

val t_let_abstract : int -> Vsym.t -> expr -> tactic 

val t_let_unfold : int -> tactic

val t_norm_tuple_proj : tactic
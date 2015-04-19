(*s Types and conversion functions for parsed types, expressions, games, proof scripts, and tactics. *)

(*i*)
open Expr
open Type
open Game
open Syms
open TheoryTypes
open ParserTypes
(*i*)

exception ParseError of string

val fail_parse : string -> 'a

val create_var : vmap -> theory_state -> string qual -> string -> ty -> Vsym.t

(*c functions that take a [theory_state] extend the state
    with lenvars and groupvars *)

val ty_of_parse_ty : theory_state -> parse_ty -> ty

val mk_Tuple : expr list -> expr

val bind_of_parse_bind :
  vmap -> theory_state -> (string * string) list -> (Vsym.t * Hsym.t) list

val expr_of_parse_expr : vmap -> theory_state -> parse_expr -> expr

val lcmd_of_parse_lcmd : vmap -> theory_state -> lcmd -> Game.lcmd

val odef_of_parse_odef :
  vmap -> theory_state -> string * string list * odec -> Game.odef

val gcmd_of_parse_gcmd : vmap -> theory_state -> gcmd -> Game.gcmd

val gdef_of_parse_gdef : vmap -> theory_state -> gcmd list -> Game.gcmd list

val se_of_parse_se : vmap -> theory_state -> gcmd list -> parse_expr -> sec_exp

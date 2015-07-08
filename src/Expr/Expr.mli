(*s Typed algebraic expression. *)

(*i*)
open Type
open Syms
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \hd{Expressions} *)

type proj_type = Type.ty * Type.ty * Type.ty

type cnst =
    GGen
  | FNat of int
  | Z
  | B of bool

val cnst_hash : cnst -> int

type op =
    GExp of Groupvar.id
  | GLog of Groupvar.id
  | GInv
  | FOpp
  | FMinus
  | FInv
  | FDiv
  | Eq
  | Not
  | Ifte
  | EMap of Esym.t

val op_hash : op -> int

type nop =
    FPlus
  | FMult
  | Xor
  | Land
  | GMult

val nop_hash : nop -> int

type expr = private { e_node : expr_node; e_ty : Type.ty; e_tag : int; }
and expr_node =
    V of Vsym.t
  | H of Hsym.t * expr
  | Tuple of expr list
  | Proj of int * expr
  | Cnst of cnst
  | App of op * expr list
  | Nary of nop * expr list
  | All of (Vsym.t list * Oracle.t) list * expr
  | Perm of Psym.t * bool * expr * expr  (*r OW permutation (f,is_inverse,Key,e) *)
  | GetPK of expr           (*r Public Key of f required by f *)  
  | GetSK of expr           (*r Secret Key of f required by f_inv *)


val e_equal : expr -> expr -> bool
val e_hash : expr -> int
val e_compare : expr -> expr -> int

module Hse : Hashcons.S with type t = expr

module Se : Set.S with type elt = expr
module He : Hashtbl.S with type key = expr
module Me : Map.S with type key = expr

(*i ----------------------------------------------------------------------- i*)
(* \hd{Constructor functions} *)

val ensure_ty_G : Type.ty -> string -> Type.Groupvar.id
val ensure_ty_KeyPair : Type.ty -> string -> Type.Permvar.id
val ensure_ty_PKey : Type.ty -> string -> Type.Permvar.id
val ensure_ty_SKey : Type.ty -> string -> Type.Permvar.id

exception TypeError of (ty *  ty * expr * expr option * string)

val mk_V      : Vsym.t -> expr
val mk_App    : op -> expr list -> ty -> expr
val mk_Nary   : nop -> expr list -> expr
val mk_H      : Hsym.t -> expr -> expr
val mk_Perm   : Psym.t -> bool -> expr -> expr -> expr
val mk_GetPK  : expr -> expr
val mk_GetSK  : expr -> expr			    
val mk_All    : (Vsym.t list * Oracle.t) list -> expr -> expr
val mk_Tuple  : expr list -> expr
val mk_Proj   : int -> expr -> expr
val mk_GGen   : Groupvar.id -> expr
val mk_GOne   : Groupvar.id -> expr
val mk_FNat   : int -> expr
val mk_FOne   : expr
val mk_FZ     : expr
val mk_Z      : Lenvar.id -> expr
val mk_B      : bool -> expr
val mk_True   : expr
val mk_False  : expr
val mk_GMult  : expr list -> expr
val mk_GExp   : expr -> expr -> expr
val mk_GLog   : expr -> expr
val mk_GInv   : expr -> expr
val mk_EMap   : Esym.t -> expr -> expr -> expr
val mk_FOpp   : expr -> expr
val mk_FMinus : expr -> expr -> expr
val mk_FInv   : expr -> expr
val mk_FDiv   : expr -> expr -> expr
val mk_Eq     : expr -> expr -> expr
val mk_Not    : expr -> expr
val mk_Ifte   : expr -> expr -> expr -> expr
val mk_FPlus  : expr list -> expr
val mk_FMult  : expr list -> expr
val mk_Xor    : expr list -> expr
val mk_Land   : expr list -> expr

(*i ----------------------------------------------------------------------- i*)
(* \hd{Generic functions on [expr]} *)

(** [e_sub_map f e] non-recursively applies [f] to all direct sub-expressions of [e], e.g.,
    if [e=Xor(a,b)] then a new term [Xor(f a, f b)] is returned.
    [e_sub_map] saves hashcons calls by detecting when [f] returns
    its argument unchanged.
    [e_sub_map] raises an exception if [f] changes the type. *)
val e_sub_map : (expr -> expr) -> expr -> expr

(** [e_fold f acc e] applies [f] to all direct sub-expressions of [e], e.g.,
    the results for [e=Xor(a,b)] is [f (f acc a) b]. *)
val e_sub_fold : ('a -> expr -> 'a) -> 'a -> expr -> 'a

(** [e_sub_iter f e] executes [f] for all direct sub-expressions of [e]
    for [f] s side-effects. *)
val e_sub_iter : (expr -> unit) -> expr -> unit

(** [e_iter f e] executes [f] for all sub-expressions of [e] (including e)
    for [f] s side-effects. *)
val e_iter : (expr -> 'b) -> expr -> unit

(** [e_exists p e] returns [true] if there is a subterms of [e] (including
    [e] itself) that satisfies [p]. *)
val e_exists : (expr -> bool) -> expr -> bool

(** [e_forall p e] returns [true] if all subterms of [e]
    (including [e] itself) satisfy [p]. *)
val e_forall : (expr -> bool) -> expr -> bool

(** [e_find p e] return the first [e'] that is a subterm of [e] and satisfies [p].
    If there is no such [e'], then [Not_found] is raised *)
val e_find : (expr -> bool) -> expr -> expr

(** [e_find_all p e] returns the the set of all [e'] that are subterms
    of [e] and satisfy [p]. *)
val e_find_all : (expr -> bool) -> expr -> Se.t

(** [e_map f e] applies [f] recursively to all subterms of [e] proceeding
    in a bottom-up fashion. *)
val e_map : (expr -> expr) -> expr -> expr

val e_map_ty_maximal : ty -> (expr -> expr) -> expr -> expr

(** [e_map_top f e] applies [f] recursively to all subterms of [e] proceeding
    in a top-down fashion. If [f] raises [Not_found], then [e_map_top]
    proceeds by applying [f] to the direct sub-expressions of the given
    expression. Otherwise, it returns without applying [f] to the subexpressions.  *)
val e_map_top : (expr -> expr) -> expr -> expr

(** [e_replace e1 e2 e] replaces all occurences of [e1] in [e] with [e2] *)
val e_replace : expr -> expr -> expr -> expr

(** [e_subst s e] replaces all occurences (in [e]) of elements [e1]
    in [dom(s)] with [s(e1)]. *)
val e_subst : expr Me.t -> expr -> expr

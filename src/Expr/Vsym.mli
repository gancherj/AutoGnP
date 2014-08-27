(** Variable symbols. *)
open Type
open IdType
open Util

type 'a gt = private { id : 'a Id.gid; ty : 'a gty; }
type t = internal gt
type et = exported gt
val export : t -> et
val hash : t -> int
val equal : t -> t -> bool
val compare : t -> t -> int
val mk : string -> ty -> t
val mke : string -> int -> ety -> et
val pp : F.formatter -> 'a gt -> unit
val tostring : 'a gt -> string
module M : Map.S with type key = t
module S : Set.S with type elt = t
module H : Hashtbl.S with type key = t

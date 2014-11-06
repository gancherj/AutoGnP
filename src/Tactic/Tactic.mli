(*s Tactic engine: transformations of proof states. *)

(*i*)
open Game
open Abbrevs
open TheoryTypes
open ParserTypes
(*i*)

val pp_jus   : int -> F.formatter -> judgment list -> unit

val handle_instr : bool -> theory_state -> instr -> theory_state * string

val eval_theory : string -> theory_state

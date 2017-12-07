(* Grobner basis computations for K[X]-module *)
#use "topfind";;
#require "num";;
(* Imports and abbreviations *)

    
open List;;
open Num;;

(*
open NormField;;
open Util;;
open ExprUtils;;
open Expr;;
open Type;;

let log_i _ls  = ()
*)
(* ------------------------------------------------------------------------- *)
(*  Utility functions                                                        *)
(* ------------------------------------------------------------------------- *)
  
let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec lexord_lt ord l1 l2 =
  match (l1,l2) with
    ([],[]) -> false
   |([],_) -> true
   |(_,[]) -> false
   | (h1::t1,h2::t2) -> if ord h1 h2 then true
                       else h1 = h2 && lexord_lt ord t1 t2;;
let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t;;


let rec distinctpairs l =
  match l with
   x::t -> itlist (fun y a -> (x,y) :: a) t (distinctpairs t)
  | [] -> [];;

(* ------------------------------------------------------------------------- *)
(* Defining polynomial types                                                 *)
(* ------------------------------------------------------------------------- *)

type id_var = int;;

type id_size = int;;

type vars = id_var list;;

type mon =
  { coeff : Num.num;
    vars : vars;
    length : int;
    size : id_size * id_size;
  };;

type pol = mon list;;

(* type pol_i = mon list * Expr.expr; *)

type i_var_set = int list;;

let mk_vmon (i:id_var) (size: id_size*id_size) :mon=
  {coeff = Num.Int 1; vars = [i]; length = 1; size};; 

(* ------------------------------------------------------------------------- *)
(* Operations on monomials.                                                  *)
(* ------------------------------------------------------------------------- *)

let veq_mon (m1:mon) (m2:mon) =
  (m1.length = m2.length ) && m1.vars=m2.vars;;

let mmul (m1:mon) (m2:mon) :mon  =
 if snd(m1.size) = fst(m2.size) then
  { coeff = m1.coeff*/m2.coeff;
    vars = m1.vars@m2.vars;
    length = m1.length + m2.length;
    size = (fst(m1.size),snd(m2.size));
  }
 else failwith "Monoms sizes uncompatible";;

exception NotPrefix;;

let rec is_prefix (m1:id_var list) (m2:id_var list) =
  match (m1,m2) with
     ([],[])-> ([],[])
    |([],m)-> ([],m)
    |(m,[]) -> (m,[])
    |(p1::q1,p2::q2) -> if p1 = p2 then 
                            is_prefix q1 q2
                        else
                           raise NotPrefix;;


(* ------------------------------------------------------------------------- *)
(* Monomial ordering.                                                        *)
(* ------------------------------------------------------------------------- *)

let morder_lt m1 m2 =
  m1.length < m2.length || m1.length = m2.length &&  lexord_lt(<) m1.vars m2.vars;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic on canonical multivariate polynomials.                         *)
(* ------------------------------------------------------------------------- *)

let mpoly_cmul c (pol:pol) :pol =
  if c = Int 0 then []
  else map (fun m -> {m with coeff=c*/m.coeff}) pol;;

let mpoly_mmul cm (pol:pol) :pol = map (mmul cm) pol;;

let mpoly_neg (pol) :pol = map (fun m -> {m with coeff=minus_num m.coeff}) pol ;;

let rec mpoly_add (l1:pol) (l2:pol):pol =
  match (l1,l2) with
    ([],_) -> l2
  | (_,[]) -> l1
  | (m1::o1,m2::o2) ->
        if veq_mon m1 m2 then
          let c = m1.coeff+/m2.coeff and rest = mpoly_add o1 o2 in
          if c = Num.Int 0 then rest
          else {m1 with coeff=c}::rest
        else if morder_lt m2 m1 then m1::(mpoly_add o1 l2)
        else m2::(mpoly_add l1 o2);;

let rec mpoly_mul l1 l2 =
  match (l1,l2) with
    (_,[]) -> []
   |([],_)-> []
   |(p::q,l2) -> mpoly_add (mpoly_mmul p l2) (mpoly_mul q l2);;

let mpoly_sub l1 l2 = mpoly_add l1 (mpoly_neg l2);;

(* ------------------------------------------------------------------------- *)

module DBase : sig 
  type t

  val create : unit -> t
  val add : t -> pol -> unit

  val get_all_prefix : t -> vars -> (pol list) list 

end = struct 

  type t = 
    { mutable t_pols : pol list;
      mutable t_allp : pol list;
              t_sons : (id_var, t) Hashtbl.t }

  let create () = 
    { t_pols = [];
      t_allp = [];
      t_sons = Hashtbl.create 17; }

  let get_vson t v =
    try Some (Hashtbl.find t.t_sons v)
    with Not_found -> None 

  let getupd_vson t v =
    try Hashtbl.find t.t_sons v 
    with Not_found ->
      let t' = create () in
      Hashtbl.add t.t_sons v t';
      t'
    
  let add t p = 
    match p with
    | [] -> ()
    | m::_ ->
      let rec aux t vs = 
        t.t_allp <- p :: t.t_allp;
        match vs with
        | []      -> t.t_pols <- p :: t.t_pols
        | v :: vs -> aux (getupd_vson t v) vs in
      aux t m.vars
                 
  let get_all_prefix =
    let rec aux ps t vs = 
      match vs with 
      | [] -> ps 
      | v:: vs ->
        match get_vson t v with 
        | None -> ps
        | Some t -> aux (t.t_pols :: ps) t vs in
    aux []

end


(* ------------------------------------------------------------------------- *)
(* Reduction of a polynom with respect to a base.                            *)
(* ------------------------------------------------------------------------- *)

(* return all the product K of polys such that the leading term of K is equal m *)
(* TODO this is wrong ! *)
let rec get_all_products (m:id_var list) (polys:pol list) : pol list list =                  
    match polys with
      [] -> []
    | (pol)::rpolys ->
       if pol = [] then get_all_products m rpolys
       else
         let h = List.hd pol in
         try let (u,v) = is_prefix h.vars m in
             if v=[] && u!=[] then get_all_products m rpolys
             else if v=[] && u=[] then [pol]::(get_all_products m rpolys)
             else let sub_sols = get_all_products v polys in
                  (List.map (fun a-> pol::a) sub_sols)@(get_all_products m rpolys)
         with NotPrefix -> get_all_products m rpolys;;



(* return all the possible one step reductions of a polynom wrt a base *)
let reduce_1 (p:pol) (polys:pol list) =
  match p with
    [] -> []
   |m::_ -> let prods = get_all_products m.vars polys in
            if prods = [] then []
            else
              let prods = List.map (fun prod ->
                  match prod with
                    [] -> []
                   |p1::q1 -> List.fold_left (fun p acc -> mpoly_mul p acc ) p1 q1 
                            ) prods in
              List.map (fun prod ->
                  match prod with
                    [] -> []
                   |m1::_ -> mpoly_sub p (mpoly_cmul (m.coeff//m1.coeff)  prod) 
                ) prods;; 
              
(* compute all the possible reductions of p wrt polys *)
let rec reduce (p:pol) (polys:pol list)=
  let reduced_1 = reduce_1 p polys in
  if reduced_1 = [] then [p]
  else List.flatten (List.map (fun p -> reduce p polys) reduced_1);;


(* ------------------------------------------------------------------------- *)
(* Computation of critical pairs.                                            *)
(* ------------------------------------------------------------------------- *)

(*
let rec monom_critical_pairs (m1 :id_var list) (m2:id_var list) : pol*pol list =
  match is_prefix m1 m2 with
    ([],[]) -> ([],[])
  | ;;

 *)

(* Exemples *)
let m1 = {coeff=Num.Int 1; vars=[1]; size=(2,2); length=1};;
let m2 = {coeff=Num.Int 1; vars=[1;2]; size=(2,4); length=2};;
let m3 = {coeff=Num.Int 1; vars=[1;1;2;]; size=(2,4); length=3};;
let m4 = {coeff=Num.Int 1; vars=[1;1]; size=(2,2); length=2};;
let m5 = {coeff=Num.Int 1; vars=[2]; size=(2,4); length=1};;

let p1 = mpoly_add [m1] [m2];;
mpoly_mul [m1] [m2;m1];;

reduce_1 [m3] [[m2;m4];[m5;m3]];;
reduce [m3;m1] [[m4;m1];[m5];[m2;m1];[m1]];;

mmul m1 m2;;


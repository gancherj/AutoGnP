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

let rec lexord ord l1 l2 =
  match (l1,l2) with
    (h1::t1,h2::t2) -> if ord h1 h2 then true
                       else h1 = h2 && lexord ord t1 t2
  | _ -> false;;

let rec tryfind f l =
  match l with
      [] -> failwith "tryfind"
    | (h::t) -> try f h with Failure _ -> tryfind f t;;


let rec distinctpairs l =
  match l with
   x::t -> itlist (fun y a -> (x,y) :: a) t (distinctpairs t)
  | [] -> [];;

(*
let gexp e h =
  if is_FOne h then e
  else if is_FZ h then mk_GExp (mk_GGen (destr_G_exn e.e_ty)) h
  else mk_GExp e h;;

let gmult e1 e2 =
  if is_GOne e1 then e2
  else if is_GOne e2 then e1
  else mk_GMult [e1; e2]  ;;
*)
(* ------------------------------------------------------------------------- *)
(* Defining polynomial types                                                 *)
(* ------------------------------------------------------------------------- *)

type id_var = int;;

type id_size = int;;

type mon =
  { coeff : Num.num;
    vars : id_var list;
    length : int;
    size : id_size * id_size;
  };;

type pol = mon list;;

(* type pol_i = mon list * Expr.expr; *)

type i_var_set = int list;;
  
(* ------------------------------------------------------------------------- *)
(* Operations on monomials.                                                  *)
(* ------------------------------------------------------------------------- *)

let mmul (m1:mon) (m2:mon) :mon  =
  { coeff = m1.coeff*/m2.coeff;
    vars = m1.vars@m2.vars;
    length = m1.length + m2.length;
    size = (fst(m1.size),snd(m2.size));
  };;

let rec is_prefix (m1:id_var list) (m2:id_var list) =
  match (m1,m2) with
     ([],[])-> ([],[])
    |([],m)-> ([],m)
    |(m,[]) -> (m,[])
    |(p1::q1,p2::q2) -> if p1 = p2 then 
                            is_prefix q1 q2
                        else
                           failwith "Not prefix"

                             

(* ------------------------------------------------------------------------- *)
(* Monomial ordering.                                                        *)
(* ------------------------------------------------------------------------- *)

let morder_lt m1 m2 =
  m1.length < m2.length || m1.length = m2.length &&  lexord(>) m1.vars m2.vars;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic on canonical multivariate polynomials.                         *)
(* ------------------------------------------------------------------------- *)

let mpoly_cmul c (pol:pol) :pol =
  if c = Int 0 then []
  else map (fun {coeff;vars;length;size} -> {coeff = c*/coeff;vars;length;size}) pol;;

let mpoly_mmul cm (pol:pol) :pol = map (mmul cm) pol;;

let mpoly_neg (pol) :pol = map (fun {coeff; vars; length; size} -> {coeff=minus_num coeff; vars; length; size}) pol ;;

let rec mpoly_add (l1:pol) (l2:pol):pol =
  match (l1,l2) with
    ([],_) -> l2
  | (_,[]) -> l1
  | (m1::o1,m2::o2) ->
        if m1.vars = m2.vars then
          let c = m1.coeff+/m2.coeff and rest = mpoly_add o1 o2 in
          if c = Num.Int 0 then rest else {coeff=c;vars=m1.vars;length=m1.length;size=m1.size}::rest
        else if morder_lt m2 m1 then m1::(mpoly_add o1 l2)
        else m2::(mpoly_add l1 o2);;

let rec mpoly_mul l1 l2 =
  match (l1,l2) with
    (_,[]) -> []
   |([],_)-> []
   |(p::q,l2) -> mpoly_add (mpoly_mmul p l2) (mpoly_mul q l2);;

let mpoly_sub l1 l2 = mpoly_add l1 (mpoly_neg l2);;

(* ------------------------------------------------------------------------- *)
(* Reduction of a polynom with respect to a base.                            *)
(* ------------------------------------------------------------------------- *)

(* return all the product K of polys sucht that the leading term of K cancels m *)
let rec get_all_products (m:id_var list) (polys:pol list) =                  
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
         with Failure _ -> get_all_products m rpolys;;

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


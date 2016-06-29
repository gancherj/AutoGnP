(* Grobner basis computations for K[X]-module *)

(* Imports and abbreviations *)


open List;;
open Num;;
open NormField;;
open Util;;
open ExprUtils;;
open Expr;;
(*open Type;;*)

(* let log_i _ls  = () *)

let mk_log level = mk_logger "Deduce.GroebnerBasis" level "GroebnerBasis.ml"
let log_i = mk_log Bolt.Level.INFO

(* ------------------------------------------------------------------------- *)
(*  Utility functions                                                        *)
(* ------------------------------------------------------------------------- *)

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;

let rec lexord ord l1 l2 =
  match (l1,l2) with
    (h1::t1,h2::t2) -> if ord h1 h2 then length t1 = length t2
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


let rec funpow n f x =
  if n < 1 then x else funpow (n-1) f (f x);;

let gexp e h =
  if is_FOne h then e
  else if is_FZ h then mk_GExp (mk_GGen (Type.destr_G_exn e.e_ty)) h
  else mk_GExp e h;;
let gmult e1 e2 =
  if is_GOne e1 then e2
  else if is_GOne e2 then e1
  else mk_GMult [e1; e2]  ;;


let rec subset l = 
  match l with
  | [] -> [[]] 
  | (h::tl) ->
    let second = subset tl in
    append (map (fun x -> h::x) second) second;;


(* ------------------------------------------------------------------------- *)
(* Defining polynomial types                                                 *)
(* ------------------------------------------------------------------------- *)

type mon = Num.num * int list;;

type pol = mon list;;

type pol_i = mon list * Expr.expr;;


type i_var_set = int list;;



(* ------------------------------------------------------------------------- *)
(* Conversions functions                                                     *)
(* ------------------------------------------------------------------------- *)





let poly_to_ipoly vars (p:pol) : Poly.ipoly =
  Poly.IP.from_terms @@ map (fun (c,m) -> ((map2 (fun pow t-> (t,pow)) m vars, ((big_int_of_num c)))) ) p;;


let polys_to_eps polys vars mp =
  let polys,invs = List.split polys in

  let ipolys = map (poly_to_ipoly vars) polys in
  combine (map (fun p -> import_ipoly "Groebner converter" p mp) ipolys) invs;;


(* ------------------------------------------------------------------------- *)
(* Operations on monomials.                                                  *)
(* ------------------------------------------------------------------------- *)

let mmul ((c1,m1):mon) ((c2,m2):mon) :mon  = (c1*/c2,map2 (+) m1 m2);;

let mdiv (pvars:i_var_set)=
  let index_sub n1 n2 = if n1 < n2 then failwith "mdiv" else n1-n2 in
  fun ((c1,m1):mon) ((c2,m2):mon) -> let pows = map2 index_sub m1 m2 in
    let checker = List.combine pows pvars in
    if (List.fold_left (fun  a (x,y) -> (y=1 && x>0)|| a ) false checker) then failwith "mdiv" else
      ((c1//c2,pows):mon);;

let mlcm ((_,m1):mon) ((_,m2):mon) :mon= (Int 1,map2 max m1 m2);;

let expr_of_monom vars mp k_Fq (m:mon)=
  let expr =  (fst (hd (polys_to_eps [([m],mk_FNat 0)] vars mp)))
              |> Expr.e_subst (me_of_list  (k_Fq)) in
  log_i (lazy (fsprintf "expr_of_mon %a" pp_expr expr));
  expr
;;

(* ------------------------------------------------------------------------- *)
(* Monomial ordering.                                                        *)
(* ------------------------------------------------------------------------- *)

let morder_lt m1 m2 =
  let n1 = itlist (+) m1 0 and n2 = itlist (+) m2 0 in
  n1 < n2 || n1 = n2 &&  lexord(>) m1 m2;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic on canonical multivariate polynomials.                         *)
(* ------------------------------------------------------------------------- *)


let mpoly_mmul_aux cm (pol:pol) :pol= map (mmul cm) pol;;

let mpoly_mmul vars mp k_fQ cm ((pol,inv):pol_i) :pol_i= (mpoly_mmul_aux cm pol, gexp inv (expr_of_monom vars mp k_fQ cm));;

let mpoly_neg_aux (pol:pol) : pol = map (fun (c,m) -> (minus_num c,m)) pol 

let mpoly_neg ((pol,inv):pol_i) :pol_i= mpoly_neg_aux pol, gexp inv (mk_FOpp (mk_FNat (1)));;


let mpoly_const (vars) c :pol=
  if c =/ Int 0 then [] else [c,map (fun _ -> 0) vars];;

let rec mpoly_add_aux (l1:pol) (l2:pol):pol =
  match (l1,l2) with
    ([],l2) -> l2
  | (l1,[]) -> l1
  | ((c1,m1)::o1,(c2,m2)::o2) ->
    if m1 = m2 then
      let c = c1+/c2 and rest = mpoly_add_aux o1 o2 in
      if c = Int 0 then rest else (c,m1)::rest
    else if morder_lt m2 m1 then (c1,m1)::(mpoly_add_aux o1 l2)
    else (c2,m2)::(mpoly_add_aux l1 o2);;

let mpoly_add ((l1,i1):pol_i) ((l2,i2):pol_i):pol_i =
  log_i (lazy (fsprintf "madd %a %a" pp_expr i1 pp_expr i2));
  (* match (l1,l2) with
     ([],l2) -> (l2,i2)
     | (l1,[]) -> (l1,i1)
     | _ ->*)
  (mpoly_add_aux l1 l2, gmult i1 i2);;

let mpoly_sub l1 l2 = mpoly_add l1 (mpoly_neg l2);;


let ipoly_to_poly vars (p:Poly.ipoly) : pol =
  let pol = Poly.IP.to_terms p in
  fold_right (fun (m,c) acc ->mpoly_add_aux [(num_of_big_int c, map (fun i  -> try assoc (i) m
                                                                      with Not_found -> 0
                                                                    ) vars  )] acc ) pol (mpoly_const vars (Int 0));;

let eps_to_polys (eps:(NormField.EP.t * Expr.expr) list )=
  let exprs,invs = List.split eps in

  let ipolys, mp = ep_to_ip exprs in
  let vars = Hashtbl.fold (fun i _ acc -> i::acc) mp [] in
  (combine (map (ipoly_to_poly vars) ipolys) invs),vars,mp;;

(* ------------------------------------------------------------------------- *)
(* Reduce monomial cm by polynomial pol, returning replacement for cm.       *)
(* ------------------------------------------------------------------------- *)

let reduce1 vars mp k_fQ cm ((pol,i),pvars) =
  match pol with
    [] -> failwith "reduce1"
  | hm::cms -> let c,m = mdiv pvars cm hm in mpoly_mmul vars mp k_fQ (minus_num c,m) (cms,i);;

(* ------------------------------------------------------------------------- *)
(* Try this for all polynomials in a basis.                                  *)
(* ------------------------------------------------------------------------- *)

let reduceb  vars mp k_fQ cm pols = let res = tryfind (reduce1 vars mp k_fQ cm) pols in
  log_i (lazy (fsprintf "reduceb %a " pp_expr (snd res)));
  res
;;

(* ------------------------------------------------------------------------- *)
(* Reduction of a polynomial (always picking largest monomial possible).     *)
(* ------------------------------------------------------------------------- *)

let rec reduce  vars mp k_fQ pols (pol,i) :pol_i=
  let [(debug,d2)] =  (polys_to_eps [(pol,i)] vars mp)  in
  log_i (lazy (fsprintf "reduce %a et %a " pp_expr debug pp_expr d2 ));
  match pol with
    [] -> ([],i)
  | cm::ptl -> try reduce  vars mp k_fQ pols (mpoly_add (reduceb  vars mp k_fQ cm pols) (ptl,i))
    with Failure _ -> let pol,inv = (reduce  vars mp k_fQ pols (ptl,i)) in
      cm::pol,inv
;;

(* ------------------------------------------------------------------------- *)
(* Compute S-polynomial of two polynomials.                                  *)
(* ------------------------------------------------------------------------- *)

let spoly  vars mp k_fQ  ((pol1,i1),pvar1) ((pol2,i2),pvar2) :pol_i=
  let gt = Type.destr_G_exn i1.e_ty in

  match (pol1,pol2) with
    ([],_) -> ([],gexp (mk_GGen gt) (mk_FNat 0))
  | (_,[]) -> ([],gexp (mk_GGen gt) (mk_FNat 0))
  | (m1::ptl1,m2::ptl2) ->
    let m = mlcm m1 m2 in


    let res = mpoly_sub (mpoly_mmul  vars mp k_fQ  (mdiv pvar1 m m1) (ptl1,i1))
        (mpoly_mmul vars mp k_fQ  (mdiv pvar2 m m2) (ptl2,i2)) in
    let [(debug,d2)] =  (polys_to_eps [res] vars mp)  in
    log_i (lazy (fsprintf "spoly_res %a et %a " pp_expr debug pp_expr d2 ));
    res

;;

(* ------------------------------------------------------------------------- *)
(* Grobner basis algorithm for free multi-module                             *)
(* ------------------------------------------------------------------------- *)


let rec grobner vars mp k_fQ basis pairs =
  (*print_string(string_of_int(length basis)^" basis elements and "^
               string_of_int(length pairs)^" pairs");
    print_newline();*)
  match pairs with
    [] -> basis
  | (p1,p2)::opairs ->
    try
      let sp = reduce vars mp k_fQ basis (spoly vars mp k_fQ p1 p2) in
      log_i (lazy (fsprintf "sp %a " pp_expr (snd sp)));

      if fst sp = [] then grobner vars mp k_fQ basis opairs

      (*else if for_all (for_all ()) sp then basis*) else
        let sp_pvars = map2 (fun x y -> x +y - x*y) (snd p1) (snd p2) in
        let newcps = map (fun p -> p,(sp,sp_pvars)) basis in
        grobner vars mp k_fQ ((sp,sp_pvars)::basis) (opairs @ newcps)    
    with Failure _ -> grobner vars mp k_fQ basis opairs;;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let groebner vars mp k_fQ basis = grobner vars mp k_fQ basis (distinctpairs basis);;

let get_inverter vars mp k_fQ basis pol =
  let red,inverter =  reduce vars mp k_fQ basis pol in
  (red= [],inverter);; 







(* ------------------------------------------------------------------------- *)
(* Arithmetic on canonical fractional multivariate polynomials.              *)
(* ------------------------------------------------------------------------- *)

type frac = pol * pol;;

type frac_r = frac * frac;; (* the second frac will represent the bijection applied to the variable*)
type gen = frac*i_var_set*bool;;
(* gen =  polynom, the set of private variables and bool =true means that we can also divide *) 
type basis = gen list;;

type gen_r = frac_r*i_var_set*bool;;
(* gen =  polynom, the set of private variables and bool =true means that we can also divide *) 
type basis_r = gen_r list;;


let unit vars :pol= [(Int 1,map (fun _ -> 0) vars)];;
let munit mon :pol =   [(Int 1,map (fun _->0) mon )];; 

let frac_neg ((nom,dem):frac) :frac = (mpoly_neg_aux nom,dem) ;;


let rec mpoly_mul (l1:pol) l2 =
  match l1 with
    [] -> []
  | (h1::t1) -> mpoly_add_aux (mpoly_mmul_aux h1 l2) (mpoly_mul t1 l2);;

let mpoly_euclid_div =
  let rec f = fun (p1:pol) (p2:pol) -> (* not (is_null_poly (p2)) *)
    if p1 = [] then ([], [])
    else
      let a1 = hd (p1) and a2 = hd (p2) in
      try
        let (c,m) = mdiv (map (fun _->0) (snd a2)) a1 a2 in
        let p = mpoly_mmul_aux (minus_num c,m) p2  in
        let p1_1 = mpoly_add_aux p1 p in
        let (q, r) = f p1_1 p2  in
        ((mpoly_add_aux [(c,m)] q), r)
      with Failure _ -> ([], p1)

  in
  fun p1 p2 -> if not (p2 = [] ) then f p1 p2
    else failwith ("euclid_div_poly : requires a non-null polynomial as its second argument");;

let mpoly_gcd  vars p q =
  let p = poly_to_ipoly vars p and q = poly_to_ipoly vars q in
  let res = Factory.gcd p q in
  ipoly_to_poly vars res;;

let mpoly_lcm vars p q =
  fst @@ mpoly_euclid_div (mpoly_mul p q) (mpoly_gcd vars p q);;


let mpoly_factor  vars p  =
  let p = poly_to_ipoly vars p in
  let res = Factory.factor p in
  map (fun (x,y) -> ipoly_to_poly vars x,y) res;;

let mpoly_pow vars l n =
  funpow n (mpoly_mul l) (mpoly_const vars (Int 1));;

let simp vars ((nom,dem):frac) :frac=
  let unit= munit (snd (hd dem)) in
  if nom = [] then  ([],unit )
  else let q = mpoly_gcd vars nom dem in
    let (p,q) = (fst @@ mpoly_euclid_div nom q,fst @@ mpoly_euclid_div dem q) in
    let minusunit =mpoly_neg_aux unit   in
    if q = minusunit then
      (mpoly_mmul_aux (hd minusunit) p, unit)
    else
      (p,q)
;;


let frac_const (vars) c :frac=
  (mpoly_const vars c,unit vars);;

let mpoly_var vars x :pol=
  [Int 1,map (fun y -> if y = x then 1 else 0) vars];;

let frac_var vars x :frac=
  (mpoly_var vars x,unit vars);;


let frac_mul vars ((n1,d1):frac) ((n2,d2):frac) =
  simp vars (mpoly_mul n1 n2,mpoly_mul d1 d2);;

let frac_div vars f (n2,d2) =
  frac_mul vars f (d2,n2) ;;


let frac_add vars ((n1,d1):frac) ((n2,d2):frac):frac =
  simp vars (mpoly_add_aux (mpoly_mul n1 d2) (mpoly_mul n2 d1),mpoly_mul d1 d2);;

let frac_sub l1 l2 = frac_add l1 (frac_neg l2);; 


(* ------------------------------------------------------------------------- *)
(* Convertion functions                                                      *)
(* ------------------------------------------------------------------------- *)

let eps_to_fracs (eps:(NormField.EP.t * Expr.expr) list ) =
  let polys,vars,mp = eps_to_polys eps in
  map (fun (p,_) -> (p, unit vars)) polys,vars,mp

let fracs_to_eps fracs vars mp =
  let frac1,frac2 = List.split fracs in
  let frac1 = polys_to_eps (map (fun p-> (p,[])) frac1) vars mp |> map (fun (p,_)->p) in
  let frac2 = polys_to_eps (map (fun p-> (p,[])) frac2) vars mp |> map (fun (p,_)->p) in
  map2 (fun nom dem -> Expr.mk_FDiv nom dem) frac1 frac2

(* ------------------------------------------------------------------------- *)
(* Reduce monomial cm by polynomial pol, returning replacement for cm.       *)
(* ------------------------------------------------------------------------- *)
let fdiv_cond vars mp (pvars:i_var_set) (div_allowed:bool) (p:frac) (q:frac) :frac=
  let res = frac_div vars p q in
  let [(debug)] =  (fracs_to_eps [res] vars mp)  in

  log_i (lazy (fsprintf "fdiv %a " pp_expr debug  ));
  if (not div_allowed) &&  (snd res)<> (unit pvars) then
    failwith "mdiv";
  iter (fun ((_,m):mon)-> let checker = List.combine m pvars in
         if (List.fold_left (fun  a (x,y) -> (y=1 && x>0)|| a ) false checker) then failwith "mdiv") ((fst res)@(snd res));
  res;;

let freduce1 vars mp (cm:frac) ((((pol,q),inv),pvars,div_allowed):gen_r) =
  match pol with
    [] -> failwith "reduce1"
  | hm::cms -> let multiplier = fdiv_cond vars mp pvars div_allowed cm ([hm],q)  in frac_mul vars (frac_neg multiplier)  (cms,q), frac_mul vars (frac_neg multiplier) inv;;

(* ------------------------------------------------------------------------- *)
(* Try this for all polynomials in a basis.                                  *)
(* ------------------------------------------------------------------------- *)

let freduceb vars mp cm (pols:gen_r list) = tryfind (freduce1 vars mp cm) pols;;

(* ------------------------------------------------------------------------- *)
(* Reduction of a polynomial (always picking largest monomial possible).     *)
(* ------------------------------------------------------------------------- *)

let rec freduce vars mp (pols:gen_r list) (((p,q),inv):frac_r) =
  let [(debug)] =  (fracs_to_eps [(p,q)] vars mp)  in
  log_i (lazy (fsprintf "reduce %a " pp_expr debug  ));
  match p with
  |  [] -> let (_,vars,_) = hd pols in
    let [(debug)] =  (fracs_to_eps [(p,q)] vars mp)  in
    log_i (lazy (fsprintf "reduce2 %a " pp_expr debug  ));
    ([],unit vars),frac_const vars (Int 0)
  | cm::ptl -> try
      let _,inv2 = (freduceb vars mp (cm::ptl,q) pols) in
      ([],munit @@ snd cm), frac_add vars inv2 inv
    with Failure _ -> try
        let [(debug)] =  (fracs_to_eps [([cm],q)] vars mp)  in
        log_i (lazy (fsprintf "reduce3 %a " pp_expr debug  ));
        let new_pol,inv2 = freduceb vars mp ([cm],q) pols in
        freduce vars mp pols (frac_add vars new_pol (ptl,q), frac_add vars inv inv2)
      with Failure _ ->                  log_i (lazy (fsprintf "reduce4 "   ));
        let new_pol,inv2 = freduce vars mp pols ((ptl,q),inv) in 
        frac_add vars ([cm],q) new_pol, frac_add vars inv2 inv ;;

(* ------------------------------------------------------------------------- *)
(* Compute S-polynomial of two polynomials.                                  *)
(* ------------------------------------------------------------------------- *)

let fspoly vars mp (gen1:gen_r) (gen2:gen_r) =
  let (((p1,q1),i1),pvar1,div_allowed1)=gen1 and (((p2,q2),i2),pvar2,div_allowed2) = gen2 in
  try
    match (p1,p2) with
      ([],_) -> ([],unit pvar1), ([],unit pvar1)
    | (_,[]) -> ([],unit pvar1), ([],unit pvar1)
    | (m1::ptl1,m2::ptl2) ->
      let m = mlcm m1 m2 and q = mpoly_lcm pvar1 q1 q2 in
      let fact = simp vars ([m],q) in
      let [(debug)] =  (fracs_to_eps [([m1],q1)] vars mp)  in
      log_i (lazy (fsprintf "m1 : %a " pp_expr debug));
      let [(debug)] =  (fracs_to_eps [([m2],q2)] vars mp)  in
      log_i (lazy (fsprintf "m2 : %a " pp_expr debug));
      let [(debug)] =  (fracs_to_eps [(ptl1,q1)] vars mp)  in
      log_i (lazy (fsprintf "ptl1 : %a " pp_expr debug));
      let [(debug)] =  (fracs_to_eps [(ptl2,q2)] vars mp)  in
      log_i (lazy (fsprintf "ptl2 : %a " pp_expr debug));
      let [(debug)] =  (fracs_to_eps [([m],q)] vars mp)  in
      log_i (lazy (fsprintf "m : %a " pp_expr debug));   
      let mult1 = fdiv_cond vars mp pvar1 div_allowed1 fact ([m1],q1) in
      log_i (lazy (fsprintf "mult1_succ " ));

      let mult2 = fdiv_cond vars mp pvar2 div_allowed2 fact ([m2],q2) in

      frac_sub vars (frac_mul vars mult1 (ptl1,q1))
        (frac_mul vars mult2 (ptl2,q2))
      ,
      frac_sub vars (frac_mul vars mult1 i1)
        (frac_mul vars mult2 i2)
  with Failure "mdiv" ->   ([],unit pvar1), ([],unit pvar1) (*try freduce vars mp [gen2] ((p1,q1),i1)
                                                              with Failure "mdiv" -> freduce vars mp [gen1] ((p2,q2),i2)*);;

let is_indep (pol:pol) pvars =
  fold_left (fun acc ((_,m):mon)-> let checker = List.combine m pvars in
              acc && not (List.fold_left (fun  a (x,y) -> (y=1 && x>0)|| a ) false checker))
    true pol

(* ------------------------------------------------------------------------- *)
(* Grobner basis algorithm for free multi-module                             *)
(* ------------------------------------------------------------------------- *)

let rec fgrobner pg vars mp (basis:basis_r) pairs =
  (*print_string(string_of_int(length basis)^" basis elements and "^
                string_of_int(length pairs)^" pairs");
    print_newline();*)

  let fracs = map (fun ((f,_),_,_)-> f ) basis in
  let debugs =  (fracs_to_eps fracs vars mp)  in
  iter   (fun debug->    log_i (lazy (fsprintf "GB %a " pp_expr debug  ))) debugs;

  let fracs = map (fun ((_,f),_,_)-> f ) basis in
  let debugs =  (fracs_to_eps fracs vars mp)  in
  iter   (fun debug->    log_i (lazy (fsprintf "inver %a " pp_expr debug  ))) debugs;
  match pairs with
    [] -> basis
  | (p1,p2)::opairs ->
    try
      let spoly = fspoly vars mp p1 p2 in
      let [(debug)] =  (fracs_to_eps [fst spoly] vars mp)  in

      log_i (lazy (fsprintf "spoly %a " pp_expr debug  ));
      let (d1,_,_) = p1 and (d2,_,_) = p2 in
      let [(debug)] =  (fracs_to_eps [fst d1] vars mp)  in

      log_i (lazy (fsprintf "from %a " pp_expr debug  ));
      let [(debug)] =  (fracs_to_eps [fst d2] vars mp)  in

      log_i (lazy (fsprintf "and %a " pp_expr debug  ));
      let sp = freduce vars mp basis (fspoly vars mp p1 p2) in
      (*map (fun (x,y)-> print_string "toto";print_int @@ int_of_num x) (fst sp); *) 
      if fst (fst sp) = [] then fgrobner pg vars mp basis opairs
      else
        (let [(debug)] =  (fracs_to_eps [fst sp] vars mp)  in
         log_i (lazy (fsprintf "sp %a " pp_expr debug  ));
         let [(debug)] =  (fracs_to_eps [fst sp] vars mp)  in
         log_i (lazy (fsprintf " %a " pp_expr debug  ));
         let (_,pv1,da1) = p1 and (_,pv2,da2) = p2 in
         if not pg then (
           let sp_pvars = map2 (fun x y -> x +y - x*y) pv1 pv2 in
           let new_gen = (sp,sp_pvars,da1&&da2) in
           let newcps = map (fun p -> p,new_gen) basis in
           fgrobner pg vars mp (new_gen::basis) (opairs @ newcps)
         )
         else (
           log_i (lazy (fsprintf " t0 " ));
           if da1 &&da2 then
             ( log_i (lazy (fsprintf " t1 " ));

               let sp_pvars = map2 (fun x y -> x +y - x*y) pv1 pv2 in
               let new_gen = (sp,sp_pvars,da1&&da2) in
               let newcps = map (fun p -> p,new_gen) basis in
               fgrobner pg vars mp (new_gen::basis) (opairs @ newcps))
           else if da1 then
             (log_i (lazy (fsprintf " t2 " ));

              let new_gen = (sp,pv1,da1) in
              let newcps = map (fun p -> p,new_gen) basis in
              fgrobner pg vars mp (new_gen::basis) (opairs @ newcps))
           else if da2 then
             (log_i (lazy (fsprintf " t3 " ));

              let new_gen = (sp,pv2,da2) in
              let newcps = map (fun p -> p,new_gen) basis in
              fgrobner pg vars mp (new_gen::basis) (opairs @ newcps))
           else
             let sp_pvars = map2 (fun x y -> x +y - x*y) pv1 pv2 in
             let new_gen = (sp,sp_pvars,da1&&da2) in
             let newcps = map (fun p -> p,new_gen) basis in
             fgrobner pg vars mp (new_gen::basis) (opairs @ newcps)
         )


        )
    with Failure "mdiv" -> fgrobner pg vars mp basis opairs;;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let fgroebner ?preserve_gen:(pg=false) vars mp basis = fgrobner pg vars mp basis (distinctpairs basis);;


(* ------------------------------------------------------------------------- *)
(* Intersection of GB                                                        *)
(* ------------------------------------------------------------------------- *)


let add_var_aux ((nom,dem):frac) :frac= 
  (map (fun (c,m) -> (c,0::m)) nom,map (fun (c,m) -> (c,0::m)) dem);;


let add_var (fracs:frac_r list) :frac_r list= 
  map (fun (f,i) -> add_var_aux f,add_var_aux i) fracs;;

let rec tsplit list =
  match list with
  |[] -> ([],[],[])
  |(a,b,c)::q -> let (x,y,z) = tsplit q in (a::x,b::y,c::z)  ;;       

let rec tcombine l1 l2 l3 =
  match l1,l2,l3 with
  |[],[],[] -> []
  | (a::x,b::y,c::z) -> let tail  = tcombine x y z  in (a,b,c)::tail  ;;

let fintersect vars mp (gen1:basis_r) (gen2:basis_r) :basis_r =
  let max_int_var = fold_right (fun var acc -> if acc< var then var else acc) vars 0 in

  let fresh_var = max_int_var+1 (* Expr.mk_V (Syms.VarSym.mk ("plopi") (Type.mk_ty Type.Int)) *) in
  let fresh_expr i = Expr.mk_V (Syms.VarSym.mk ("inter"^(string_of_int i)) (Type.mk_ty Type.Fq)) in
  Hashtbl.add mp fresh_var (fresh_expr fresh_var);
  let fracs,pvars,da = tsplit gen1 in
  let fracs2,pvars2,da2 = tsplit gen2 in
  let vars = fresh_var::vars in
  let fracs  = add_var fracs and fracs2 = add_var fracs2 in
  let pvars = map (fun x-> 1::x) pvars and   pvars2 = map (fun x-> 1::x) pvars2 in
  let t_poly =  frac_var vars fresh_var in
  let mt_poly = frac_sub vars (frac_const vars (Int (1)) ) t_poly in 
  (*map (fun p -> printert (term_of_poly (vars) p)) (List.map (mpoly_mul mt_poly) pols2) ;print_newline();*)
  let basis = fgroebner ~preserve_gen:true vars mp ((tcombine (List.map (fun (f,i)-> frac_mul vars t_poly f, frac_mul vars t_poly i) fracs) pvars da)@(tcombine (List.map (fun (f,i)-> frac_mul vars mt_poly f, frac_mul vars t_poly i) fracs2) pvars2 da2)) in
  (*map printert (map (fun (x,y)-> term_of_poly (vars) x) (basis));print_newline();*)

  (* we only keep polynoms independant of plop *)
  let reduce_basis = fold_right (fun (((nom,dem),(inv1,inv2)),pvars,da) acc -> if
                                  for_all (fun x-> hd  (snd x) = 0) nom
                                  &&
                                  for_all (fun x-> hd  (snd x) = 0) dem
                                  then (((( map (fun (c,m) -> (c,tl m)) nom),( map (fun (c,m) -> (c,tl m)) dem)),(map (fun (c,m) -> (c,tl m)) inv1,map (fun (c,m) -> (c,tl m)) inv2) ),tl pvars,da)::acc
                                  else acc ) basis [] in

  reduce_basis;;

(* ------------------------------------------------------------------------- *)
(* Rnd Deduce                                                                *)
(* ------------------------------------------------------------------------- *)

let simp_gen vars (gen:gen_r) =
  let (((p,q),i), pvars, div_allowed) = gen in
  if div_allowed then
    let p= mpoly_factor vars p and q = mpoly_factor vars q in
    let p = filter (fun (pol,_)->  not (is_indep pol pvars) ) p and  q = filter (fun (pol,_)->  not (is_indep pol pvars) ) q in
    let p = fold_right (fun (pol,pow) acc -> mpoly_mul acc (mpoly_pow pvars pol pow)) p (mpoly_const pvars (Int 1))
    and q =  fold_right (fun (pol,pow) acc -> mpoly_mul acc (mpoly_pow pvars pol pow)) q (mpoly_const pvars (Int 1)) in
    ((simp vars (p,q),i), pvars, div_allowed) 
  else gen;;


let split_poly vars poly rnd_vars =
  let rnd_vars = fst (List.split rnd_vars) in
  let res1 = map (fun var->List.filter (fun (_,mon) ->  fold_right2 (fun u v w -> (u<>var || v=1)&& w)  vars mon true ) poly  ) (rnd_vars) in
  let remainder = List.filter (fun (_,mon) ->  fold_right2 (fun u v w -> (not (mem u rnd_vars )|| v=0)&& w)  vars mon true ) poly in
  let res = (remainder,( map (map (fun (c,mon)-> c,map2 (fun x y-> if mem x rnd_vars then 0 else y)vars mon) )res1)) in
  if length(concat ((fst res)::(snd res))) = length poly then
    res
  else
    failwith "non linear";;

let rnd_deduce (vars:int list) mp rndvars pvars fracs ((pol,q):frac) :basis_r=
  let pvars = map (fun x -> if mem x pvars then 1 else 0 ) vars in
  let (remainder,splits) = split_poly vars pol rndvars in
  iter   (fun debug->    log_i (lazy (fsprintf "var %i, %a " debug pp_expr (Hashtbl.find mp debug)))) vars;
  iteri   (fun i debug->    log_i (lazy (fsprintf "var num %i is p : %i " debug i))) pvars;

  iter   (fun (debug,l)->    log_i (lazy (fsprintf "rnd_var %i " debug));
           iter (fun debug-> log_i (lazy (fsprintf "indeps %i " debug))) l ) rndvars;

  if concat splits = [] then
    (
      log_i (lazy (fsprintf "r 0.1"  ));

      let left_gen = (map (fun p->(p,([],munit pvars)),pvars,false) fracs) in
      let right_basis = [(((remainder,q),([],munit pvars)), map (fun _ -> 1 ) vars,false)] in
      let global_basis = fintersect vars mp left_gen (right_basis) in
      log_i (lazy (fsprintf "r 0.2"  ));

      global_basis
    )
  else
    (
      log_i (lazy (fsprintf "r 1"  ));

      let left_gen = (((remainder,q), frac_const vars (Int 0) ), map (fun _ -> 1 ) vars,false)::(map (fun p->(p, frac_const vars (Int 0) ) ,pvars,false) fracs) in
      let left_gen = filter (fun (((u,_),_),_,_)-> u <> []) left_gen in
      let left_basis = fgroebner vars mp left_gen in


      let fracs = map (fun ((f,_),_,_)-> f ) (left_basis) in
      let debugs =  (fracs_to_eps fracs vars mp)  in
      iter2   (fun debug  ((_,_),puvars,bl)->    log_i (lazy (fsprintf "Gen_l %a " pp_expr debug  ));
                iteri  (fun i debug->    log_i (lazy (fsprintf "var %i is pu : %i " i debug  ))) puvars;
                if bl then  log_i (lazy (fsprintf "div allowed"   )))
        debugs left_basis;


      log_i (lazy (fsprintf "r 2"  ));


      let right_basis = map2 (fun poly (x,puvars)-> let rev_puvars =  map (fun y -> if mem y puvars then 0 else 1 ) vars
                               in
                               [(((poly,q),frac_var vars x),rev_puvars,true);((frac_mul vars (poly,q) (frac_var vars x),(frac_mul vars (frac_var vars x) (frac_var vars x))),rev_puvars,true)] ) splits rndvars in

      let fracs = map (fun ((f,_),_,_)-> f ) (concat right_basis) in
      let debugs =  (fracs_to_eps fracs vars mp)  in
      iter   (fun debug->    log_i (lazy (fsprintf "Gen_r_1 %a " pp_expr debug  ))) debugs;


      let right_basis = filter (fun (((u,_),_),_,_)-> u <> []) (concat right_basis) in

      let right_basis = map (simp_gen vars) right_basis in

      let fracs = map (fun ((f,_),_,_)-> f ) (right_basis) in
      let debugs =  (fracs_to_eps fracs vars mp)  in
      iter2   (fun debug  ((_,_),puvars,bl)->    log_i (lazy (fsprintf "Gen_r_2 %a " pp_expr debug  ));
                iteri  (fun i debug->    log_i (lazy (fsprintf "var %i is pu : %i " i debug  ))) puvars;
                if bl then  log_i (lazy (fsprintf "div allowed"   )))
        debugs right_basis;



      log_i (lazy (fsprintf "r 3"  ));
      let fracs = map (fun ((f,_),_,_)-> f ) right_basis in
      let debugs =  (fracs_to_eps fracs vars mp)  in
      iter   (fun debug->    log_i (lazy (fsprintf "Gen_r %a " pp_expr debug  ))) debugs;

      let global_basis = fintersect vars mp left_basis (right_basis) in
      log_i (lazy (fsprintf "r 4"  ));

      let fracs = map (fun ((f,_),_,_)-> f ) (global_basis) in
      let debugs =  (fracs_to_eps fracs vars mp)  in
      iter2   (fun debug  ((_,_),puvars,bl)->    log_i (lazy (fsprintf "Gen_f %a " pp_expr debug  ));
                iteri  (fun i debug->    log_i (lazy (fsprintf "var %i is pu : %i " i debug  ))) puvars;
                if bl then  log_i (lazy (fsprintf "div allowed"   )))
        debugs global_basis;

      global_basis
    )






let add_vars_aux ((nom,dem):frac) vars :frac=
  let nvars = map (fun _->0) vars in 
  (map (fun (c,m) -> (c,m@nvars)) nom,map (fun (c,m) -> (c,m@nvars)) dem);;


let add_vars (fracs:frac list) vars :frac list= 
  map (fun f -> add_vars_aux f vars) fracs;;

let global_rnd_deduce mh vars rndvars pvars poly_pub_list poly_sec_list =
  let fresh_expr i = Expr.mk_V (Syms.VarSym.mk ("plop"^(string_of_int i)) (Type.mk_ty Type.Fq)) in
  let max_int_var = fold_right (fun var acc -> if acc< var then var else acc) vars 0 in
  let fresh_nu_vars = mapi (fun i _ -> i+1+max_int_var) poly_sec_list in
  iter (fun i-> Hashtbl.add mh i (fresh_expr i)) fresh_nu_vars;
  let vars = vars@fresh_nu_vars in
  let pols_sec = add_vars poly_sec_list fresh_nu_vars and pols_pub = add_vars poly_pub_list fresh_nu_vars in
  let pols_sec = map2 (fun pol var_nu -> frac_mul vars (frac_var vars var_nu) pol) pols_sec fresh_nu_vars in
  let nu_pol_sec = fold_right (fun pol acc -> frac_add vars pol acc) pols_sec (frac_const vars (Int 0)) in
  let rndvars = subset rndvars in
  fold_right (fun rnd_vars acc ->
      if acc <> [] then acc 
      else if rnd_vars <> [] then

        (
          let gens = rnd_deduce vars mh rnd_vars pvars pols_pub nu_pol_sec in
          log_i (lazy (fsprintf "gens found %i" (List.length gens)  ));

          let fracs = map (fun ((f,_),_,_)-> f ) (gens) in
          let debugs =  (fracs_to_eps fracs vars mh)  in
          iter2   (fun debug  ((_,q),puvars,bl)->    log_i (lazy (fsprintf "Gen %a " pp_expr debug  ));
                    let [(debug2)] =  (fracs_to_eps [q] vars mh)  in

                    log_i (lazy (fsprintf "invert %a " pp_expr debug2  ));
                    iteri  (fun i debug->    log_i (lazy (fsprintf "var %i is pu : %i " i debug  ))) puvars;
                    if bl then  log_i (lazy (fsprintf "div allowed"   )))
            debugs gens;

          if gens = [] then []
          else
            (
              let red,rnds =  freduce vars mh gens (nu_pol_sec,(frac_const vars (Int 0))) in
              log_i (lazy (fsprintf "red done"  ));
              let [(debug)] =  (fracs_to_eps [rnds] vars mh)  in

              log_i (lazy (fsprintf "rnds %a " pp_expr debug  ));
              let [(debug)] =  (fracs_to_eps [red] vars mh)  in

              log_i (lazy (fsprintf "red %a " pp_expr debug  ));
              if fst red = [] then fracs_to_eps [rnds] vars mh 

              else []
            )
        )
      else []
    ) rndvars []
;;

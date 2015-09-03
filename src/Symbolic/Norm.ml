(* * Normal form computation for expressions. *)

(* ** Imports *)
open Abbrevs
open Type
open Expr
open ExprUtils
open Syms
open Util

let _log_i ls = mk_logger "Norm" Bolt.Level.INFO "Norm" ls

(* ** Helper functions for norm
 * ----------------------------------------------------------------------- *)

(** Type based normalization for group elements and products, even
    applied to variables *)
let rec norm_type e =
  match e.e_ty.ty_node with
  | Fq | Bool | Int | BS _ | KeyPair _ | KeyElem _ -> e

  | G gv    -> mk_GExp_Gen gv (mk_GLog e)   (* g ^ (log x) *)

  | Prod lt -> mk_Tuple (List.mapi (fun i _ -> norm_type (mk_Proj i e)) lt)

let mk_proj_simpl i e =
  match e.e_node with
  | Tuple es ->
    begin try List.nth es i
    with Invalid_argument _ -> assert false
    end
  | _ -> mk_Proj i e

let common_diff xs1 xs2 =
  let rec rm acc y xs =
    match xs with
    | x::xs when x = y -> Some (L.rev_append acc xs)
    | x::xs            -> rm (x::acc) y xs
    | []               -> None
  in  
  let rec go common nc1 xs1 xs2 =
    match xs1 with
    | []  -> (common,nc1,xs2)
    | x1::xs1 ->
      begin match rm [] x1 xs2 with
      | Some xs2 -> go (x1::common) nc1 xs1 xs2
      | None     -> go common (x1::nc1) xs1 xs2
      end
  in
  go [] [] xs1 xs2

(* ** Mutually recursive norm functions
 * ----------------------------------------------------------------------- *)

let rec norm_expr ~strong e =
  match e.e_node with

  | V _ -> norm_type e

  | Quant(q,b,e) -> mk_Quant q b (norm_expr ~strong e)

  | Cnst GGen ->  mk_GExp_Gen (destr_G_exn e.e_ty) mk_FOne

  | Cnst _ -> e
  
  | Tuple l -> mk_Tuple (List.map (norm_expr ~strong) l)

  | Proj(i,e) -> mk_proj_simpl i (norm_expr ~strong e)     

  | Nary(nop, _) when is_field_nop nop -> mk_simpl_field_expr ~strong e

  | App(op, _)   when is_field_op op   -> mk_simpl_field_expr ~strong e

  | Nary(nop, l) -> mk_simpl_nop ~strong nop (List.map (norm_expr ~strong) l)
 
  | App(op, l) -> mk_simpl_op ~strong op (List.map (norm_expr ~strong) l)

and mk_simpl_op ~strong op l =
  let mk_Ifte_simp e1 e2 e3 =
    mk_simpl_op ~strong:false Ifte [e1; e2; e3]
  in
  match op, l with

  | (FunCall _ | ProjKeyElem _ | RoCall _ | RoLookup _), ([] | _::_::_) -> assert false
  | FunCall f,      [e] -> mk_FunCall f e
  | ProjKeyElem kt, [e] -> mk_ProjKeyElem kt e
  | RoCall h,       [e] -> mk_RoCall h e
  | RoLookup h,     [e] -> mk_RoLookup h e

  | Perm(_, _),([] | [_] | _::_::_::_) -> assert false
  | Perm(ptype1, f1),[k1; e1] -> (* f(pk, finv(sk, e)) = e and vice-versa *)
    let k1 = norm_expr ~strong k1 in
    let e1 = norm_expr ~strong e1 in
    begin match e1.e_node with
    | App(Perm(ptype2,f2),[k2; e2])
        when    is_ProjKeyElem (key_elem_of_perm_type ptype1) f1 k1
             && is_ProjKeyElem (key_elem_of_perm_type ptype2) f2 k2
             && Psym.equal f1 f2
             && ptype1 <> ptype2 ->
      e2
    | _ -> mk_Perm f1 ptype1 k1 e1
    end

  | GExp gv, [g1;p1] -> (* g1 is necessary of the form g ^ a *)
    let a = destr_GExp_Gen gv g1 in
    let p = mk_simpl_field_expr ~strong (mk_FMult [a; p1]) in
    mk_GExp_Gen gv p

  | GInv, [g1] ->
    let gv = ensure_ty_G g1.e_ty "norm" in
    let a  = destr_GExp_Gen gv g1 in
    let p = mk_simpl_field_expr ~strong (mk_FOpp a) in
    mk_GExp_Gen gv p

  | GLog gv, [g1] -> destr_GExp_Gen gv g1

  | EMap es, [g1;g2] -> (* e(g^a,g^b) -> e(g,g)^ab *)
    let p1 = destr_GExp_Gen es.Esym.source1 g1 in
    let p2 = destr_GExp_Gen es.Esym.source2 g2 in
    let p = mk_simpl_field_expr ~strong (mk_FMult [p1; p2]) in
    mk_GExp_Gen es.Esym.target p

  | Eq, [e1;e2] when is_False e1            -> norm_expr ~strong (mk_Not e2)
  | Eq, [e1;e2] when is_False e2            -> norm_expr ~strong (mk_Not e1)
  | Eq, [e1;e2] when is_True e1             -> e2
  | Eq, [e1;e2] when is_True e2             -> e1
  | Eq, [e1;e2] when equal_expr e1 e2       -> mk_True
  | Eq, [e1;e2] when equal_ty e1.e_ty mk_Fq ->
    let e = mk_simpl_field_expr ~strong:true (mk_FMinus e1 e2) in
    if equal_expr e mk_FOne || equal_expr e (mk_FOpp mk_FOne)
    then mk_False
    else mk_Eq e1 e2
  | Eq, [e1;e2]                             -> mk_Eq e1 e2

  | Not, [e] when is_True e  -> mk_False
  | Not, [e] when is_False e -> mk_True
  | Not, [e] ->
    begin match e.e_node with
    | App(Not,[e]) -> e
    | Quant(q,b,e) -> mk_Quant (neg_quant q) b (norm_expr ~strong (mk_Not e))
    | _            -> mk_Not e
    end

  | Ifte, [e1;e2;e3] ->
    if is_True e1 then e2
    else if is_False e1 then e3
    else if equal_expr e2 e3 then e2
    else if is_FPlus e2 || is_FPlus e3 then (
      let destr_nofail e =
        if is_FPlus e then destr_FPlus e else [e]
      in
      let mk_nofail = function
        | [] -> mk_FZ
        | [e] -> e
        | es  -> mk_FPlus es
      in
      let e2s = destr_nofail e2 in
      let e3s = destr_nofail e3 in
      let common,e2s,e3s = common_diff e2s e3s in
      if common = []
      then norm_type (mk_Ifte e1 e2 e3)
      else mk_nofail ((mk_Ifte_simp e1 (mk_nofail e2s) (mk_nofail e3s))::common)
    ) else if is_GExp e2 && is_GExp e3 then (
      let (e2_1,e2_2) = destr_GExp e2 in
      let (e3_1,e3_2) = destr_GExp e3 in
      if equal_expr e2_1 e3_1 && not (is_GLog e2_2 || is_GLog e3_2)
      then mk_GExp e2_1 (mk_Ifte_simp e1 e2_2 e3_2)
      else norm_type (mk_Ifte e1 e2 e3)
    ) else norm_type (mk_Ifte e1 e2 e3)

  | ( GExp _ | GLog _ | EMap _ | GInv
    | FOpp   | FMinus | FInv   | FDiv
    | Eq     | Ifte   | Not ), _ ->
    assert false

and mk_simpl_nop ~strong op l =
  match op with

  | FPlus  | FMult  -> assert false
  
  | GMult ->
    let gv = match l with e::_ -> destr_G_exn e.e_ty | _ -> assert false in
    let l = List.map (destr_GExp_Gen gv) l in
    let p = mk_simpl_field_expr ~strong (mk_FPlus l) in
    mk_GExp_Gen gv p

  (* We disable this for now
  | Xor when is_Prod e.e_ty ->
    let tys = destr_Prod_exn e.e_ty in
    let prod_list_of_e e' =
      if e'.e_ty <> e.e_ty then
        failwith "Wrong tuple type";
      match e'.e_node with
      | Tuple l -> List.map (norm_expr ~strong) l
      | _ ->
        let e' = norm_expr ~strong e' in
        List.mapi (fun i _ -> norm_expr ~strong (mk_Proj i e')) tys
    in
    let xor_of_tuples = List.map prod_list_of_e ess
    in
    let tuples_of_xor = BatList.transpose xor_of_tuples in
    mk_Tuple (List.map (mk_simpl_nop ~strong Xor) tuples_of_xor)
  *)

  | Xor ->
    let l = List.flatten (List.map destr_Xor_nofail l) in
    let l = List.sort compare_expr l in
    let e = List.hd l in
    let rec aux l =
      match l with
      | [] | [_] -> l
      | e1::((e2::l) as l1) ->
        if equal_expr e1 e2 then aux l else e1 :: aux l1
    in
    L.iter (fun e -> F.printf "%a " pp_expr e) l;
    let l = aux l in
    let l = List.filter (fun e -> not (is_Zero e)) l in
    if l = [] then mk_Zero e.e_ty
    else mk_Xor (aux l)
 
  | Land ->
    let l = List.flatten (List.map destr_Land_nofail l) in
    let l = if strong then List.sort compare_expr l else l in
    let rec aux l =
      match l with
      | [] -> []
      | [e] ->
        if is_True e then []
        else if is_False e then raise Not_found
        else l
      | e1::((e2::_) as l1) ->
        if is_False e1 then raise Not_found
        else if equal_expr e1 e2 || is_True e1 then aux l1
        else e1 :: aux l1
    in
    try
      let l = aux l in
      if l = [] then mk_True
      else mk_Land l
    with Not_found -> mk_False

and mk_simpl_field_expr ~strong e =
  let norm_subexpr e =
    match e.e_node with

    | Cnst (FNat _)
    | App (FOpp,[_])     | App (FInv,[_])
    | App (FMinus,[_;_]) | App (FDiv,[_;_])
    | Nary (FPlus, _)    | Nary (FMult, _)  -> e

    | App(GLog gv, [e]) ->
      begin try destr_GExp_Gen gv (norm_expr ~strong e)
      with _ -> assert false
      end

    | _ -> norm_expr ~strong e
  in
  CAS.norm norm_subexpr e

let norm_expr_weak = norm_expr ~strong:true

let norm_expr_strong = norm_expr ~strong:false

(** use norm_expr to check equality modulo equational theory *)
let equalmod_expr e e' = equal_expr (norm_expr_strong e) (norm_expr_strong e')

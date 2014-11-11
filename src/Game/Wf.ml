(*s Well-formedness of games. *)

(*i*)
open Abbrevs
open Util
open Expr
open ExprUtils
open Type
open Game
open Syms
open Gsyms
open Norm

let log_t ls = mk_logger "Logic.Wf" Bolt.Level.TRACE "Wf" ls
let _log_d ls = mk_logger "Logic.Wf" Bolt.Level.DEBUG "Wf" ls
let log_i ls = mk_logger "Logic.Wf" Bolt.Level.INFO "Wf" ls
(*i*)

exception Wf_var_undef of Vsym.t * expr

exception Wf_div_zero of expr list

let assert_exc c rf = if not c then rf ()

type wf_check_type = CheckDivZero | NoCheckDivZero

type wf_state = {
  wf_names : Sstring.t;  (*r used names for variables, adversaries, and oracles *)
  wf_bvars : Vsym.S.t;   (*r bound variables, never two vsyms with the same name *)
  wf_nzero : expr option (*r product of all nonzero-assumptions for field-expressions *)
}

let mk_wfs () = {
  wf_names = Sstring.empty;
  wf_bvars = Vsym.S.empty;
  wf_nzero = None
}

let ensure_name_fresh wfs name =
  if Sstring.mem name wfs.wf_names
  then failwith "duplicate name (variables, oracles, and adversaries)"
  else { wfs with wf_names = Sstring.add name wfs.wf_names }

let ensure_names_fresh wfs names =
  List.fold_left ensure_name_fresh wfs names

let ensure_varname_fresh wfs vs =
  let name = Id.name vs.Vsym.id in
  let wfs = ensure_name_fresh wfs name in
  { wfs with wf_bvars = Vsym.S.add vs wfs.wf_bvars }

let ensure_varnames_fresh wfs vs =
  List.fold_left ensure_varname_fresh wfs vs

let ty_prod vs =
  match List.map (fun vs -> vs.Vsym.ty) vs with
  | [a] -> a
  | ts  -> mk_Prod ts

let rec add_ineq ctype wfs e1 e2 =
  try
    if ctype = NoCheckDivZero then (
      wf_exp CheckDivZero wfs e1;
      wf_exp CheckDivZero wfs e2;
    );
    let e1 = norm_expr_weak e1 in
    let e2 = norm_expr_weak e2 in
    let mk_nzero a b =
      let h =
        match a.e_node, b.e_node with
        | App(FDiv,[a1;a2]), App(FDiv,[b1;b2]) ->
          norm_expr_weak (mk_FMinus (mk_FMult [a1;b2]) (mk_FMult [b1;a2]))
        | App(FDiv,[a1;a2]), _ ->
          norm_expr_weak (mk_FMinus a1 (mk_FMult [b;a2]))
        | _, App(FDiv,[b1;b2]) ->
          norm_expr_weak (mk_FMinus b1 (mk_FMult [b2;a]))
        | _ ->
          norm_expr_weak (mk_FMinus a b)
      in
      match wfs.wf_nzero with
      | None    -> Some h
      | Some nz -> Some (mk_FMult [h; nz])
    in
    match e1.e_ty.ty_node,e2.e_ty.ty_node with
    | Fq, Fq   -> { wfs with
                    wf_nzero = mk_nzero e1 e2 }
    | G _, G _ -> { wfs with
                    wf_nzero = mk_nzero (mk_GLog e1) (mk_GLog e2) }
    | _ -> wfs
  with
    (* we already checked well-formedness, at least with NoCheckDivZero *)
    _ -> wfs

and check_nonzero ctype wfs e =
  if ctype = NoCheckDivZero then true
  else (
    log_t (lazy (fsprintf "check nonzero %a" pp_exp e));
    let check e =
      match wfs.wf_nzero with
      | Some nz ->
        log_i (lazy (fsprintf "nonzero assumption: %a" pp_exp nz));
        CAS.mod_reduce nz e
      | None    -> false
    in
    (* we know e itself is division-safe *)
    let e = norm_expr_weak e in
    match e.e_node with
    | App(Ifte, [c; _a; b]) when is_False c -> check b
    | App(Ifte, [c; a; b]) when
        is_FOne a && is_Eq c && (let (u,v) = destr_Eq c in e_equal u b && is_Zero v) ->
      true
    | App(FDiv, [a;_b]) -> check a (* division-safe => b<>0 *)
    | _                 -> check e (* e is polynomial *)
  )

and wf_exp ctype wfs e0 =
  let rec go e =
    match e.e_node with
    | Cnst _ -> ()
    | V vs -> 
      assert_exc (Vsym.S.mem vs wfs.wf_bvars)
        (fun () -> raise (Wf_var_undef(vs,e)))
    | Exists(e1,e2,(vhs)) ->
      let wfs = ensure_varnames_fresh wfs (List.map fst vhs) in
      wf_exp ctype wfs e2;
      wf_exp ctype wfs e1
    | H(_,e1) | Proj(_,e1) -> go e1
    | Nary(Land,es) ->
      let is_InEq e =
        if is_App Not e then is_App Eq (destr_Not e) else false
      in
      let destr_InEq e = destr_Eq (destr_Not e) in
      let (ineqs,others) = List.partition is_InEq es in
      (* first check and add ineqs that are division-safe *)
      let ineqs =
        Util.move_front
          (fun ie -> try go ie; true with _ -> false)
          ineqs
      in
      log_t (lazy (fsprintf "add ineqs %a" (pp_list ",@ " pp_exp) ineqs));
      let wfs =
        List.fold_left
          (fun wfs e ->
            log_t (lazy (fsprintf "check & add ineq %a" pp_exp e));
            wf_exp ctype wfs e;
            let e1,e2 = destr_InEq e in
            add_ineq ctype wfs e1 e2)
          wfs
          ineqs
      in
      List.iter (wf_exp ctype wfs) others
    | App(FInv,[e]) ->
      assert_exc
        (check_nonzero ctype wfs e)
        (fun () -> raise (Wf_div_zero [e]));
      go e
    | App(FDiv,[e1;e2]) ->
      assert_exc
        (check_nonzero ctype wfs e2)
        (fun () -> raise (Wf_div_zero [e2]));
      go e1; go e2
    | Tuple(es) | Nary(_,es) | App(_,es) ->
      L.iter go es
  in
  go e0

let wf_samp ctype wfs v t es =
  assert (ty_equal v.Vsym.ty t &&
            List.for_all (fun e -> ty_equal t e.e_ty) es &&
            (es = [] || not (ty_equal t mk_Bool)));
  List.iter (wf_exp ctype wfs) es;
  let wfs = ensure_varname_fresh wfs v in
  let v = mk_V v in
  List.fold_left (fun wfs e -> add_ineq ctype wfs e v) wfs es

let wf_let ctype wfs v e =
  let wfs = ensure_varname_fresh wfs v in
  assert (ty_equal v.Vsym.ty e.e_ty);
  wf_exp ctype wfs e;
  wfs

let wf_lcmds ctype wfs0 odef0 =
  let rec go wfs odef = match odef with
    | [] -> wfs
    | LLet(v,e)::lcmds ->
      let wfs = wf_let ctype wfs v e in
      go wfs lcmds
    | LSamp(v,(t,es))::lcmds ->
      let wfs = wf_samp ctype wfs v t es in
      go wfs lcmds
    | LBind (vs,hsym)::lcmds -> 
      assert (ty_equal (ty_prod vs) hsym.Hsym.dom);
      go wfs lcmds
    | LGuard e::lcmds ->
      assert (ty_equal e.e_ty mk_Bool);
      wf_exp ctype wfs e;
      let wfs =
        match e.e_node with
        | App(Not,[eeq]) ->
            (match eeq.e_node with
             | App(Eq,[e1;e2]) -> add_ineq ctype wfs e1 e2
             | _ -> wfs)
        | _ -> wfs
      in
      go wfs lcmds
  in
  go wfs0 odef0

let wf_odef ctype wfs (osym,vs,lcmds,e,_) =
   assert (ty_equal osym.Osym.dom (ty_prod vs) &&
             ty_equal osym.Osym.codom e.e_ty);
   let wfs = ensure_varnames_fresh wfs vs in
   let wfs = wf_lcmds ctype wfs lcmds in
   wf_exp ctype wfs e

let wf_gdef ctype gdef0 =
  let rec go wfs gdef = match gdef with
    | [] -> wfs
    | GLet(v,e)::gcmds ->
      let wfs = wf_let ctype wfs v e in
      go wfs gcmds
    | GSamp(v,(t,es))::gcmds ->
      let wfs = wf_samp ctype wfs v t es in
      go wfs gcmds
    | GCall(vs,asym,e,os)::gcmds ->
      let wfs = ensure_varnames_fresh wfs vs in
      let wfs = ensure_name_fresh wfs (Id.name asym.Asym.id) in
      assert (ty_equal (ty_prod vs) asym.Asym.codom &&
                ty_equal asym.Asym.dom e.e_ty);
      let wfs =
        ensure_names_fresh wfs
          (List.map (fun (osym,_,_,_,_) -> Id.name osym.Osym.id) os)
      in
      List.iter (wf_odef ctype wfs) os;
      go wfs gcmds
  in
  go (mk_wfs ()) gdef0

let wf_se ctype se =
  let wfs = wf_gdef ctype se.se_gdef in
  assert (ty_equal mk_Bool se.se_ev.e_ty);
  wf_exp ctype wfs se.se_ev

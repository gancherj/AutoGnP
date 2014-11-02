(*s Derived tactics for dealing with assumptions. *)

(*i*)
open Util
open Nondet
open Type
open Assumption
open Syms
open Expr
open Game
open TheoryState
open Rules
open RewriteRules

module Ht = Hashtbl
module CR = CoreRules
module PU = ParserUtil

let log_t ls =
  Bolt.Logger.log "Logic.Derived" Bolt.Level.TRACE ~file:"AssumptionRules" (Lazy.force ls)

let log_d ls =
  Bolt.Logger.log "Logic.Derived" Bolt.Level.DEBUG ~file:"AssumptionRules" (Lazy.force ls)
(*i*)

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Decisional assumptions} *)

(** Compute substitution and perform let abstraction. *)
let t_assm_dec_aux assm dir subst assm_samps assm_lets  ju =
  let gdef_samps = Util.take (L.length assm_samps) (samplings ju.ju_gdef) in

  (* subst renames assm into judgment *)
  guard (list_eq_for_all2
           (fun (_,(_,(t1,_))) (_,(_,(t2,_))) -> ty_equal t1 t2)
           assm_samps gdef_samps) >>= fun _ ->
  let subst =
    L.fold_left2
      (fun s (_,(vs1,_)) (_,(vs2,_)) ->Vsym.M.add vs1 vs2 s)
      subst
      assm_samps
      gdef_samps
  in
  log_t (lazy (fsprintf "subst %a"
                 (pp_list "," (pp_pair Vsym.pp Vsym.pp)) (Vsym.M.bindings subst)));

  (* perform let abstractions *)
  let n_let = L.length assm_lets in
  let ltac (i_let,subst) (i,(vs,e)) =
    (* FIXME: use deterministic name generation / reuse name *)
    let name = CR.mk_name () in
    let vs'  = Vsym.mk name vs.Vsym.ty in
    let e'   = Game.subst_v_e (fun vs -> Vsym.M.find vs subst) e in
    ( (i_let + 1, Vsym.M.add vs vs' subst)
    , t_let_abstract i vs' (norm_expr_def e') None
      @>
      (* We assume the last let definition differs between left and right
         and therefore enforce that it is used in the game *)
      (if i_let = n_let then
          (t_guard (fun ju -> Se.mem (mk_V vs') (Game.read_ju ju)))
       else
          CR.t_id)
    )
  in
  let priv_exprs = L.map (fun (_,(v,_)) -> mk_V v) gdef_samps in
  let ((_,subst), let_abstrs) =  map_accum ltac (1,subst) assm_lets in

  (* try conversion between gdef = gprefix;grest and inst(assm);grest *)
  let conv_common_prefix ju =
    let a_rn = ad_inst subst assm in
    let c = if dir = LeftToRight then a_rn.ad_prefix1 else a_rn.ad_prefix2 in
    let grest = Util.drop (L.length c) ju.ju_gdef in
    (   CoreRules.t_conv true { ju with ju_gdef=c@grest }
     @> CoreRules.t_assm_dec dir subst [] assm) ju
  in
  try
    ((*  t_print "after swapping, before unknown"
     @> *) t_norm_unknown priv_exprs
     (* @> t_print "after unknown" *)
     @> t_seq_list let_abstrs
     (* @> t_print "after let" *)
     @> (CoreRules.t_assm_dec dir subst [] assm @|| conv_common_prefix)) ju
  with
    Invalid_rule s -> log_t (lazy s); mempty

(** We known which samplings in the assumption are equivalent, so we
    extract the corresponding samplings in the judgment and make sure
    that equivalent samplings are order *)
let ordered_eqclass samp_assm match_samps eq_class =
  let eq_class_pos =
    samp_assm
    |> L.mapi (fun i (_,(vs,_)) -> if L.mem vs eq_class then Some i else None)
    |> cat_Some
  in
  let match_samp_pos =
    L.map (fun i -> fst (L.nth match_samps i)) eq_class_pos
  in
  L.sort compare match_samp_pos =  match_samp_pos

let match_samps symvars assm_samps_typed gdef_samps_typed =
  let rec go acc asts gsts =
    match asts,gsts with
    | [], [] ->
      ret acc
    | (t,asamps)::asts, (t',gsamps)::gsts ->
      assert (ty_equal t t');
      pick_set_exact (L.length asamps) (mconcat gsamps) >>= fun match_samps ->
      permutations match_samps >>= fun match_samps ->
      let ordered eq_class = ordered_eqclass asamps match_samps eq_class in
      guard (L.for_all ordered symvars) >>= fun _ ->
      let old_new_pos =
        L.map (fun (sg,ss) -> (fst sg, fst ss)) (L.combine match_samps asamps)
      in
      go (acc@old_new_pos) asts gsts 
    | _ ->
      assert false
  in
  go [] assm_samps_typed gdef_samps_typed

(** Fuzzy matching with given assumption, compute sequence of swap
    applications that make assumption applicable. Compute sequence of
    let abstraction applications in next step. *)
let t_assm_dec_auto assm dir subst ju =
  log_t (lazy "###############################");
  log_t (lazy (fsprintf "t_assm_dec_auto dir=%s ad=%s" (string_of_dir dir) assm.ad_name));

  (* extract samplings and lets from assumption and judgment *)
  let assm_cmds  = if dir=LeftToRight then assm.ad_prefix1 else assm.ad_prefix2 in
  let assm_samps = samplings assm_cmds in
  let assm_lets  = lets assm_cmds in
  let gdef_samps = samplings ju.ju_gdef in
  log_t (lazy (fsprintf "@[assm samps:@\n%a@]" (pp_list "@\n" pp_samp) assm_samps));
  log_t (lazy (fsprintf "@[assm lets:@\n%a@]" (pp_list "@\n" pp_let)  assm_lets));
  log_t (lazy (fsprintf "@[gdef samplings:@\n%a@]" (pp_list "@\n" pp_samp) gdef_samps));

  (* compute matchings between samplings in assumption and judgment (match up types) *)
  let ty_of_samp (_,(_,(t,_))) = t in
  let assm_samp_types = sorted_nub ty_compare (L.map ty_of_samp assm_samps) in
  let assm_samps_typed =
    L.map
      (fun ty -> (ty, L.filter (fun s -> ty_equal (ty_of_samp s) ty) assm_samps))
      assm_samp_types
  in
  let gdef_samps_typed =
    L.map
      (fun ty -> (ty, L.filter (fun s -> ty_equal (ty_of_samp s) ty) gdef_samps))
      assm_samp_types
  in
  match_samps assm.ad_symvars assm_samps_typed gdef_samps_typed >>= fun old_new_pos ->
  log_t (lazy (fsprintf "@[match samps:@\n[%a]@]"
                 (pp_list ", " (pp_pair pp_int pp_int)) old_new_pos));
  let swaps =
       parallel_swaps old_new_pos
    |> L.map (fun (old_pos,delta) ->
                if delta = 0 then None else Some (CR.t_swap old_pos delta))
    |> cat_Some
  in
  (t_seq_list swaps @> t_assm_dec_aux assm dir subst assm_samps assm_lets) ju

(** Supports placeholders for which all possible values are tried *)
let t_assm_dec_non_exact
    ?i_assms:(iassms=Sstring.empty) ts massm_name mdir _mrngs  mvnames ju =
  (* use assumption with given name or try all decisional assumptions *)
  (match massm_name with
   | Some aname ->
     begin try ret (Ht.find ts.ts_assms_dec aname)
     with Not_found -> tacerror "error no assumption %s" aname
     end
   | None ->
     mconcat (Ht.fold (fun _aname assm acc -> assm::acc) ts.ts_assms_dec [])
  ) >>= fun assm ->
  guard (not (Sstring.mem assm.ad_name iassms)) >>= fun _ ->
  (* use given direction or try both directions *)
  (opt ret (mconcat [LeftToRight; RightToLeft]) mdir)
  >>= fun dir ->
  (* generate substitution for all required new variable names
     generating new variable names if not enough are provided *)
  let needed = needed_vars dir assm in
  let given_vnames = from_opt [] mvnames in
  let required = max 0 (L.length needed - L.length given_vnames) in
  (* FIXME: prevent variable clashes here *)
  let generated_vnames =
    L.map (fun _ -> CR.mk_name ()) (list_from_to 0 required)
  in
  let ren = 
    L.fold_left2
      (fun sigma v x -> Vsym.M.add v (Vsym.mk x v.Vsym.ty) sigma)
      Vsym.M.empty
      needed
      (given_vnames@generated_vnames)
  in
  t_assm_dec_auto assm dir ren ju

let t_assm_dec_exact ts massm_name mdir mrngs mvnames ju =
  let dir = match mdir with Some s -> s | None -> tacerror "exact requires dir" in
  let assm_name = match massm_name with
    | Some s -> s
    | None   -> tacerror "exact requires sname"
  in
  let assm =
    try Ht.find ts.ts_assms_dec assm_name
    with Not_found -> tacerror "error no assumption %s" assm_name
  in
  let rngs = match mrngs with
    | Some rngs -> rngs
    | None      -> tacerror "exact requires ranges"
  in
  let vneeded = needed_vars dir assm in
  let acalls  = assm.ad_acalls in
  let vnames = match mvnames with
    | Some names                      -> names
    | None when L.length vneeded <> 0 -> tacerror "exact required vnames"
    | None                            -> []
  in
  if L.length vneeded <> L.length vnames then tacerror "Bad number of variables";
  if L.length acalls <> L.length rngs then tacerror "Bad number of ranges";
  let ren =
    List.fold_left2
      (fun s v x -> let v' = Vsym.mk x v.Vsym.ty in Vsym.M.add v v' s)
      Vsym.M.empty
      vneeded
      vnames
  in
  let c = if dir = LeftToRight then assm.ad_prefix1 else assm.ad_prefix2 in
  let c_ju = Util.take (List.length c) ju.ju_gdef in
  (* extend renaming with mappings for random samplings in prefix *)
  let ren =
    List.fold_left2
      (fun rn  i1 i2 ->
        match i1, i2 with
        | GSamp(x1,_), GSamp(x2,_) when Type.ty_equal x1.Vsym.ty x2.Vsym.ty ->
          Vsym.M.add x1 x2 rn
        | _ -> tacerror "assumption_decisional: can not infer renaming")
      ren c c_ju
  in
  (* extend renaming with mappings for variables binding return values *)
  let ren =
    List.fold_left2
      (fun rn  (_,j) (_asym,vres,_) ->
        let nvres = L.length vres in
        let vres_ju =
          Util.take nvres (Util.drop (j + 1 - nvres) ju.ju_gdef)
          |> L.map (function GLet (x,_) -> x | _ -> assert false)
        in
        L.fold_left2 (fun rn vs vs_ju -> Vsym.M.add vs vs_ju rn) rn vres vres_ju)
      ren rngs assm.ad_acalls
  in
  let conv_common_prefix ju =
    let a_rn = ad_inst ren assm in
    let c = if dir = LeftToRight then a_rn.ad_prefix1 else a_rn.ad_prefix2 in
    let grest = Util.drop (L.length c) ju.ju_gdef in
    (   CR.t_ensure_progress (CoreRules.t_conv true { ju with ju_gdef=c@grest })
     @> CoreRules.t_assm_dec dir ren rngs assm) ju
  in
  (CR.t_assm_dec dir ren rngs assm @|| conv_common_prefix) ju

let t_assm_dec
  ?i_assms:(iassms=Sstring.empty) ts exact massm_name mdir mrngs mvnames ju =
  if exact then
    t_assm_dec_exact ts massm_name mdir mrngs mvnames ju
  else
    t_assm_dec_non_exact ~i_assms:iassms ts massm_name mdir mrngs mvnames ju

(*i ----------------------------------------------------------------------- i*)
(* \subsection{Derived tactics for dealing with computational assumptions} *)

let e_eqs e =
  let comm_eq e =
    guard (is_Eq e) >>= fun _ ->
    ret e
  in
  if is_Land e then (
    mconcat (destr_Land e) >>= fun cj ->
    comm_eq cj
  ) else (
    comm_eq e
  )

let match_expr (var : vs) pat e =
  let binding_v = ref None in
  let ensure c =
    if not c then raise Not_found
  in
  let inst e =
    match !binding_v with
    | None    -> binding_v := Some e
    | Some e' -> ensure (e_equal e e')
  in
  let rec pmatchl es1 es2 =
    ensure (L.length es1 = L.length es2);
    L.iter2 pmatch es1 es2
  and pmatch p e =
    match p.e_node, e.e_node with
    | V(vs1),_
      when Vsym.equal vs1 var       -> inst e
    | V(vs1),        V(vs2)         -> ensure (Vsym.equal vs1 vs2)
    | H(hs1,e1),     H(hs2,e2)      -> ensure (Hsym.equal hs1 hs2); pmatch e1 e2
    | Tuple(es1),    Tuple(es2)     -> pmatchl es1 es2
    | Proj(i1,e1),   Proj(i2,e2)    -> ensure (i1 = i2); pmatch e1 e2
    | Cnst(c1),      Cnst(c2)       -> ensure (c1 = c2)
    | App(op1,es1),  App(op2,es2)   -> ensure (op1 = op2); pmatchl es1 es2
    | Nary(nop1,es1),Nary(nop2,es2) -> ensure (nop1 = nop2); pmatchl es1 es2
    | Exists(_),_                   -> raise Not_found
    | _                             -> raise Not_found
  in
  try
    pmatch pat e;
    begin match !binding_v with
    | None   -> mempty
    | Some e -> ret e
    end
  with
    Not_found ->
      mempty

let match_exprs_assm ju assm =
  let jev = ju.ju_ev in
  let aev = assm.ac_event in
  let av = assm.ac_event_var in
  let eav = mk_V av in
  (* we first collect all equalities in aev and jev *)
  e_eqs aev >>= fun aeq ->
  guard (Se.mem eav (e_vars aeq)) >>= fun _ ->
  e_eqs jev >>= fun jeq ->
  ret (aeq,jeq)

let tries = ref 0

let conj_type e =
  if is_Eq e then (
    let (a,_) = destr_Eq e in
    Some (true,a.e_ty)
  ) else if is_Not e then (
    let e = destr_Not e in
    if is_Eq e then (
      let (a,_) = destr_Eq e in
      Some (false,a.e_ty)
    ) else (
      None
    )
  ) else (
    None
  )

let t_assm_comp_match ?icases:(icases=Se.empty) before_t_assm assm subst mev_e ju =
  let assm = ac_inst subst assm in
  (match mev_e with
  | Some e -> ret e
  | None   ->
    match_exprs_assm ju assm >>= fun (pat,e) ->
    match_expr assm.ac_event_var pat e
  ) >>= fun ev_e ->
  let sassm = Assumption.ac_inst subst assm in
  let sassm_ev = e_replace (mk_V sassm.ac_event_var) ev_e sassm.ac_event in
  let assm_ju = { ju_gdef = sassm.ac_prefix; ju_ev = sassm_ev } in
  let assm_ju = norm_ju ~norm:(fun x -> x) assm_ju in
  let conjs = destr_Land assm_ju.ju_ev in
  let ineq = L.hd (L.filter is_Not conjs) in
  let nineq = norm_expr_def (mk_Not ineq) in
  guard (not (Se.mem nineq icases)) >>= fun _ ->
  let assm_tac = 
    (    CR.t_case_ev ~flip:true nineq
     @>> [ (* t_print "before_remove_ev" *)
                before_t_assm
             @> CR.t_assm_comp assm ev_e subst
         ; CR.t_id])
  in
  let sconjs = destr_Land sassm_ev in
  let sineq = L.hd (L.filter is_Not sconjs) in
  let snineq = Norm.abbrev_ggen sineq in
  if is_Land ju.ju_ev &&
     L.exists (fun e ->
       e_equal (Norm.abbrev_ggen e) snineq) (destr_Land ju.ju_ev)
  then CR.t_assm_comp assm ev_e subst ju >>= fun ps -> ret (None,ps)
  else CR.t_id ju >>= fun ps -> ret (Some assm_tac,ps)

let t_assm_comp_aux ?icases:(icases=Se.empty) before_t_assm assm mev_e ju =
  let assm_cmds = assm.ac_prefix in
  let samp_assm = samplings assm_cmds in
  let lets_assm = lets assm_cmds in
  let samp_gdef = samplings ju.ju_gdef |> Util.take (L.length samp_assm) in
  guard
    (list_eq_for_all2 (fun (_,(_,(t1,_))) (_,(_,(t2,_))) -> ty_equal t1 t2)
       samp_assm samp_gdef)
  >>= fun _ ->
  let subst =
    L.fold_left2
      (fun s (_,(vs1,_)) (_,(vs2,_)) -> Vsym.M.add vs1 vs2 s)
      Vsym.M.empty
      samp_assm
      samp_gdef
  in
  log_t (lazy (fsprintf "subst %a"
                 (pp_list "," (pp_pair Vsym.pp Vsym.pp)) (Vsym.M.bindings subst)));
  let ltac subst (i,((vs:Vsym.t),(e:expr))) =
    let name = CR.mk_name () in
    let vs'  = Vsym.mk name vs.Vsym.ty in
    let e'   = Game.subst_v_e (fun vs -> Vsym.M.find vs subst) e in
    ( Vsym.M.add vs vs' subst, t_let_abstract i vs' (Norm.norm_expr e') None)
  in
  let (subst, let_abstrs) = map_accum ltac subst lets_assm in
  incr tries;
  let t_before = t_seq_list let_abstrs in
     (* @> t_debug (fsprintf "assm_comp_auto tried %i combinations so far@\n" !tries) *)
  try
    t_before ju >>= fun ps ->
    CR.rapply_all (t_assm_comp_match ~icases (before_t_assm @> t_before) assm subst mev_e) ps
  with
    Invalid_rule s -> log_d (lazy s); mempty

let t_assm_comp_auto ?icases:(icases=Se.empty) ts assm mev_e ju =
  tries := 0;
  log_t (lazy (fsprintf "###############################"));
  log_t (lazy (fsprintf "t_assm_comp assm=%s" assm.ac_name));
  let vmap = vmap_of_globals ju.ju_gdef in
  let mev_e = map_opt (PU.expr_of_parse_expr vmap ts) mev_e in
  let assm_cmds = assm.ac_prefix in
  let samp_assm = samplings assm_cmds in
  let lets_assm = lets assm_cmds in
  let samp_gdef = samplings ju.ju_gdef in
  log_t (lazy (fsprintf "@[assm:@\n%a@]" (pp_list "@\n" pp_samp) samp_assm));
  log_t (lazy (fsprintf "@[assm:@\n%a@]" (pp_list "@\n" pp_let)  lets_assm));
  log_t (lazy (fsprintf "@[gdef:@\n%a@\n%!@]" (pp_list "@\n" pp_samp) samp_gdef));
  let assm_samp_num = L.length samp_assm in
  (* FIXME: do not assume samplings in assumption occur first and are from Fq *)
  let samp_gdef = L.filter (fun (_,(_,(ty,_))) -> ty_equal ty mk_Fq) samp_gdef in
  pick_set_exact assm_samp_num (mconcat samp_gdef) >>= fun match_samps ->
  permutations match_samps >>= fun match_samps ->
  (* try all type-preserving bijections between random samplings in
     the assumption and the considered game *)
  let ordered eq_class = ordered_eqclass samp_assm match_samps eq_class in
  guard (L.for_all ordered assm.ac_symvars) >>= fun _ ->
  
  let old_new_pos = L.mapi (fun i x -> (fst x,i)) match_samps in
  let swaps =
       parallel_swaps old_new_pos
    |> L.map (fun (old_pos,delta) ->
                if delta = 0 then None else Some (CR.t_swap old_pos delta))
    |> cat_Some
  in
  let priv_exprs = L.map (fun (_,(v,_)) -> mk_V v) match_samps in
  let excepts =
    L.map
      (fun (i,(_,(_,es))) -> if es<>[] then Some (CR.t_except i []) else None)
      match_samps
    |> cat_Some
  in
  (* FIXME: use case_ev and rfalse to handle case with missing events *)
  let remove_events =
    if not (is_Land assm.ac_event && is_Land ju.ju_ev) then ( [] )
    else (
      let ctypes = L.map conj_type (destr_Land assm.ac_event) in
      destr_Land ju.ju_ev
      |> L.mapi (fun i e -> (i,conj_type e))
      |> L.filter (fun (_,ct) -> not (L.mem ct ctypes))
      |> L.map fst
    )
  in
  let before_t_assm =
    CR.t_remove_ev remove_events
    @> t_norm_unknown priv_exprs
    @> t_seq_list excepts
    @> t_seq_list swaps
  in
  guard (not (is_Land assm.ac_event && not (is_Land ju.ju_ev))) >>= fun _ ->
  before_t_assm ju >>= fun ps ->
  CR.rapply_all (t_assm_comp_aux ~icases before_t_assm assm mev_e) ps >>= fun (ot,ps) ->
  match ot with
  | Some t -> t ju
  | None   -> ret ps
  

let t_assm_comp_no_exact ?icases:(icases=Se.empty) ts maname mev_e ju =
  (match maname with
  | Some aname ->
    begin try ret (Ht.find ts.ts_assms_comp aname)
    with Not_found -> tacerror "error no assumption %s" aname
    end
  | None ->
    mconcat (Ht.fold (fun _aname assm acc -> assm::acc) ts.ts_assms_comp [])
  ) >>= fun assm ->
  (* try all assumptions *)
  t_assm_comp_auto ~icases ts assm mev_e ju

let t_assm_comp_exact ts maname mev_e ju =
  let aname =
     match maname with
     | None ->
      tacerror "assumption_computational: event expression required for exact"
     | Some an -> an
  in
  let ev_e =
    match mev_e with
    | Some se ->
      let vmap = vmap_of_globals ju.ju_gdef in
      PU.expr_of_parse_expr vmap ts se
    | None ->
      tacerror "assumption_computational: event expression required for exact"
   in
  let assm =
    try Ht.find ts.ts_assms_comp aname
    with Not_found -> tacerror "error no assumption %s" aname
  in
  let c = assm.ac_prefix in
  let jc = Util.take (L.length c) ju.ju_gdef in
  let subst =
    L.fold_left2 (fun s i1 i2 ->
      match i1, i2 with
      | GLet(x1,_), GLet(x2,_) | GSamp(x1,_), GSamp(x2,_) 
        when Type.ty_equal x1.Vsym.ty x2.Vsym.ty ->
        Vsym.M.add x1 x2 s
      | _ ->
        tacerror "assumption_computational : can not infer substitution")
      Vsym.M.empty c jc
  in
  (CR.t_assm_comp assm ev_e subst) ju

let t_assm_comp ?icases:(icases=Se.empty) ts exact maname mev_e ju =
  if exact then
    t_assm_comp_exact ts maname mev_e ju
  else
    t_assm_comp_no_exact ~icases ts maname mev_e ju

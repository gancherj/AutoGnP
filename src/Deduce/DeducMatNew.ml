open Expr
open ExprUtils
open Util

(* TODO: stack overflows -- bug or i need to move to a heap *)

module Ht = Hashtbl

let rec subterms e = 
    match e.e_node with
    | Nary(_,es') ->
      List.fold_left Se.union Se.empty (List.map subterms es')
    | App(_, es') ->
      List.fold_left Se.union Se.empty (List.map subterms es')
    | _ ->
      Se.singleton e

let subterms' es = List.fold_left Se.union Se.empty (List.map subterms es)

let mk_log level = mk_logger "Deduce.DeducMat" level "DeducMat.ml"
let log_i = mk_log Bolt.Level.DEBUG

let norm_e e = Norm.norm_expr ~strong:true e
let norm_ei ei = (Norm.norm_expr ~strong:true (fst ei), I (Norm.norm_expr
~strong:true (expr_of_inverter (snd ei))))

let ei_op op ei = let (e,i) = ei in (op e, I (op (expr_of_inverter i)))
let ei_bop op ei1 ei2 = let (e1, i1) = ei1 in
                        let (e2, i2) = ei2 in
                        (op e1 e2, I (op (expr_of_inverter i1) (expr_of_inverter
                        i2)))

let matplus_bop e1 e2 = mk_MatPlus [e1;e2]


let trans_add etbl etbl_copy =
    Ht.iter (fun e i ->
        let (e',i') = ei_op mk_MatTrans (e,i) in
        Ht.add etbl e' i') etbl_copy

let splits_add etbl etbl_copy =
    Ht.iter (fun e i ->
        if Type.is_Mat_splittable e.e_ty then
            let (e1,i1) = ei_op mk_MatSplitLeft (e,i) in
            let (e2, i2) = ei_op mk_MatSplitRight (e,i) in
            Ht.add etbl e1 i1;
            Ht.add etbl e2 i2
        else ()) etbl_copy

    
let opp_add etbl etbl_copy =
    Ht.iter (fun e i ->
        let (e',i') = ei_op mk_MatOpp (e,i) in
        Ht.add etbl e' i') etbl_copy

        
let mul_add etbl etbl_copy =
    Ht.iter (fun e1 i1 ->
        Ht.iter (fun e2 i2 ->
            if Type.matmult_compat_ty e1.e_ty e2.e_ty then
                let (e', i') = ei_bop mk_MatMult (e1,i1) (e2, i2) in
                Ht.add etbl e' i'
            else () ) etbl_copy) etbl_copy

   
let concat_add etbl etbl_copy =
    Ht.iter (fun e1 i1 ->
        Ht.iter (fun e2 i2 ->
            if Type.concat_compat_ty e1.e_ty e2.e_ty then
                let (e', i') = ei_bop mk_MatConcat (e1,i1) (e2, i2) in
                Ht.add etbl e' i'
            else () ) etbl_copy) etbl_copy


let plus_add etbl etbl_copy =
    Ht.iter (fun e1 i1 ->
        Ht.iter (fun e2 i2 ->
            if Type.equal_ty e1.e_ty e2.e_ty then
                let (e', i') = ei_bop matplus_bop (e1,i1) (e2, i2) in
                Ht.add etbl e' i'
            else () ) etbl_copy) etbl_copy


let uniq l =
  let open List in
  let tbl = Hashtbl.create (length l) in
  let f l e = 
    try 
      let _ = Hashtbl.find tbl e in l
    with
    | Not_found -> 
      Hashtbl.add tbl e ();
      e::l
  in
  List.rev (List.fold_left f [] l)   



let extend_iter etbl etbl_orig = 
    trans_add etbl etbl_orig;
    opp_add etbl etbl_orig;
    splits_add etbl etbl_orig;
    mul_add etbl etbl_orig;
    concat_add etbl etbl_orig;
    plus_add etbl etbl_orig;
    etbl

let norm_etbl etbl =
    let etbl_new = Ht.create (Ht.length etbl) in
    Ht.iter (fun e i ->
        let (e', i') = norm_ei (e,i) in
        Ht.add etbl_new e' i') etbl;
    etbl_new

let try_find e etbl =
    let etbl_norm = norm_etbl etbl in
    try
        let i = Ht.find etbl_norm (norm_e e) in
        print_string "found!!\n";
        Some (i)
    with
    Not_found -> None


let rec try_solve etbl etbl_orig e depth =
    if depth == 0 then raise Not_found
    else
        print_string "etbl now has size: ";
        print_int (Ht.length etbl);
        print_string "\n ";
        match try_find e etbl with
        | Some i -> i
        | None -> try_solve (extend_iter etbl etbl_orig) etbl_orig e (depth - 1)

let rec create_etbl so_far ecs = match ecs with
| [] -> so_far
| (e,i) :: ecs' -> Ht.add so_far e i; create_etbl so_far ecs'

let solve_mat ecs e =
    (*log_i (lazy (fsprintf "call solve_mat:"));
    List.iter (fun ei ->
        log_i (lazy (fsprintf "(%a, %a)" pp_expr (fst ei) pp_expr
        (expr_of_inverter (snd ei))))) ecs;
    log_i (lazy (fsprintf "trying to find %a" pp_expr e)); *)
    (*let ecs = List.filter (fun ei -> not (Se.is_empty (Se.inter (subterms (fst ei))
    (subterms e)))) ecs in
    if (List.length ecs == 0) then
        raise Not_found
    else*)
    print_string "solving with relevant len = ";
    print_int (List.length ecs);
    print_string "\n";
    let etbl = create_etbl (Ht.create 50) ecs in
    let etbl_orig = Ht.copy etbl in
    try_solve etbl etbl_orig e 50 

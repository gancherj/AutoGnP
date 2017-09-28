open Expr
open Util
open ExprUtils
open Type

let rec superset es = match es with
| [] -> [[]]
| e :: es -> let ps = superset es in
             ps @ List.map (fun ss -> e :: ss) ps

let complement ss es = List.filter (fun x -> not (List.mem x ss)) es

let viable_subsets es = let subsets = superset es in
let subsets = List.filter (fun ss -> not (List.length ss < 1 || List.length es - List.length
ss < 1)) subsets in
List.map (fun ss -> (ss, complement ss es)) subsets

let all_adds es = let subsets = viable_subsets es in
List.map (fun sc -> let (s,c) = sc in (mk_MatPlus s, mk_MatPlus c))
subsets

let all_adds_lst es = viable_subsets es

let is_app op e = match e.e_node with | App(op',_) when op'=op -> true | _ -> false

let unary_app_extract op e = match e.e_node with | App(op', [e']) when op'=op ->
    e' | _ -> assert false

let plus_unary_extract op es =  mk_MatPlus (List.map (unary_app_extract op) es)

let is_mult_with_l a e = match e.e_node with | App(MatMult, [e1; e2]) when a=e1 -> true | _ -> false
let is_mult_with_r b e = match e.e_node with | App(MatMult, [e1; e2]) when b=e2 -> true | _ -> false

let extract_mult_l e = match e.e_node with | App(MatMult, [e1;e2]) -> e1 | _ -> assert false
let extract_mult_r e = match e.e_node with | App(MatMult, [e1;e2]) -> e2 | _ -> assert false

(* sum of F = F of sum for trans, opp, splits *)
let plus_unary_fold es =
            if (List.for_all (is_app MatTrans) es) then
                Some (mk_MatTrans (plus_unary_extract MatTrans es)) else
            if (List.for_all (is_app MatOpp) es) then
                Some (mk_MatOpp (plus_unary_extract MatOpp es)) else
            if (List.for_all (is_app MatSplitLeft) es) then
                Some (mk_MatSplitLeft (plus_unary_extract MatSplitLeft es)) else
            if (List.for_all (is_app MatSplitRight) es) then
                Some (mk_MatSplitRight (plus_unary_extract MatSplitRight es)) else
            None

let rec combine (xs : 'a list) (yss : 'a list list) : 'a list list =
    match yss with
    | [] -> List.map (fun x -> [x]) xs
    | _ ->
    List.flatten (List.map (fun x ->
        List.map (fun ys ->
            List.rev (x :: ys)) yss) xs)

let rec rows_of_cols (ess : 'a list list) = 
    List.fold_left (fun acc x -> combine x acc) [] ess



(* (a * b) * c -> a * (b * c) *)
let reassoc_mult to_add a b = match a.e_node, b.e_node with
    | (App(MatMult, [e1; e2]), _) -> (* re-associate to right *)
            to_add := mk_MatMult e1 (mk_MatMult e2 b) :: !to_add
    | _ -> ()

(* (tr b) * (tr a) -> tr (a * b) *)
let trans_mult_pullin to_add a b = match a.e_node, b.e_node with
    | (App(MatTrans, [e1]), App(MatTrans, [e2])) ->
            to_add := mk_MatTrans (mk_MatMult e2 e1) :: !to_add
    | _ -> ()

(* (tr a) * b -> tr ((tr b) * a) *)
let trans_mult_exp1 to_add a b = match a.e_node with
    | App(MatTrans, [e1]) ->
            to_add := mk_MatTrans (mk_MatMult (mk_MatTrans b) e1) :: !to_add
    | _ -> ()

(* a * (tr b) -> tr( b * (tr a)) *)
let trans_mult_exp2 to_add a b = match b.e_node with
    | App(MatTrans, [e2]) ->
            to_add := mk_MatTrans (mk_MatMult e2 (mk_MatTrans a)) :: !to_add
    | _ -> ()



(* a * (sp b) -> sp (a * b) (both sr and sl) *)
let split_mult_pullin to_add a b = match a.e_node, b.e_node with
    | (_, App(MatSplitLeft, [e])) ->
            to_add := mk_MatSplitLeft (mk_MatMult a e) :: !to_add
    | (_, App(MatSplitRight, [e])) ->
            to_add := mk_MatSplitRight (mk_MatMult a e) :: !to_add
    | _ -> ()


let distr_mult_expand_l to_add a b = match a.e_node, b.e_node with
    | (Nary(MatPlus, es), _) ->
            let mults = List.map (fun e -> mk_MatMult e b) es in
            to_add := mk_MatPlus mults :: !to_add
    | _ -> ()

let distr_mult_expand_r to_add a b = match a.e_node, b.e_node with
    | (_, Nary(MatPlus, es)) ->
            let mults = List.map (fun e -> mk_MatMult a e) es in
            to_add := mk_MatPlus mults :: !to_add
    | _ -> ()


(* unnorm expands e for one step, returning a list of new possibilities. *)
let rec unnorm (e : expr) : expr list =
    match e.e_node with
    | App(MatMult, [a;b]) -> 
        e :: (unnorm_mult a b)
    | Nary(MatPlus, es) ->
        let unnorms = List.map unnorm es in
        let ess = rows_of_cols unnorms in
        let new_es = List.map unnorm_plus (es :: ess) in
        e :: (List.flatten new_es)
    | App(MatTrans, [a]) ->
        let unnorms = unnorm a in
        e :: List.map mk_MatTrans unnorms
    | App(MatSplitLeft, [a]) ->
        let unnorms = unnorm a in
        e :: List.map mk_MatSplitLeft unnorms
    | App(MatSplitRight, [a]) ->
        let unnorms = unnorm a in
        e :: List.map mk_MatSplitRight unnorms
    | _ -> [e]

and unnorm_mult (a : expr) (b : expr) : expr list =
    let to_add = ref [] in
    reassoc_mult to_add a b;
    trans_mult_pullin to_add a b;
    trans_mult_exp1 to_add a b;
    trans_mult_exp2 to_add a b;
    split_mult_pullin to_add a b;
    distr_mult_expand_l to_add a b;
    distr_mult_expand_r to_add a b;
    !to_add

and unnorm_plus_multi to_add (es : expr list) = 
    if (List.length es > 2) then
        let adds = all_adds_lst es in
        List.iter (fun (a,b) ->
            match (plus_unary_fold a, plus_unary_fold b) with
            | (Some i1, Some i2) -> to_add := mk_MatPlus [i1;i2] :: !to_add;
            | (Some i1, None) -> to_add := mk_MatPlus (i1 :: b) :: !to_add;
            | (None, Some i2) -> to_add := mk_MatPlus (a @ [i2]) :: !to_add;
            | _ -> ();)
        adds
    else
        ()

(* a*b + a * c -> a * (b + c) *)
and unnorm_plus_distr_l to_add (es : expr list) = match (List.hd es).e_node with
    | App(MatMult, [e1; e2]) ->
            if List.for_all (is_mult_with_l e1) es then
                let rights = List.map extract_mult_r es in
                to_add := mk_MatMult e1 (mk_MatPlus rights) :: !to_add
            else ()
    | _ -> ()

(* a * b + c * b -> (a + c) * b *)
and unnorm_plus_distr_r to_add (es : expr list) = match (List.hd es).e_node with
    | App(MatMult, [e1; e2]) ->
            if List.for_all (is_mult_with_r e2) es then
                let lefts = List.map extract_mult_l es in
                to_add := mk_MatMult (mk_MatPlus lefts) e2 :: !to_add
            else ()
    | _ -> ()


and unnorm_plus (es : expr list) : expr list =
    let to_add = ref [mk_MatPlus es] in
    (match plus_unary_fold es with
    | Some i -> to_add := i :: !to_add;
    | _ -> ());
    unnorm_plus_multi to_add es;
    unnorm_plus_distr_l to_add es;
    unnorm_plus_distr_r to_add es;
    !to_add


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

let expand_iter es =
    uniq (List.flatten (List.map unnorm es))

let rec expand_ es depth =
    if depth == 0 then es else expand_ (expand_iter es) (depth - 1)

let expand e depth = 
    try
        expand_ [e] depth
    with
        TypeError (a,b,c,d,s) ->
            print_string s; [e]

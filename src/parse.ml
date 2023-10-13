module T = Kernel.Term
module B = Kernel.Basic
module E = Parsers.Entry

let get_new_name (set : string * string)
    (set_index : ((string * string) * int) list) =
  match List.assoc_opt set set_index with
  | None ->
      (Printf.sprintf "%c%d" (String.get (snd set) 0) 0, (set, 1) :: set_index)
  | Some i ->
      ( Printf.sprintf "%c%d" (String.get (snd set) 0) i,
        (set, i + 1) :: List.remove_assoc set set_index )

let id_name cst = B.string_of_ident @@ B.id cst
let md_name cst = B.string_of_mident @@ B.md cst
let pair_string_of_name name = (md_name name, id_name name)
let string_of_name f = md_name f ^ "." ^ id_name f
let name_eq_to name md id = md_name name = md && id_name name = id
let plth = "plth"
let logic = "logic"
let plth_const name symbol = name_eq_to name plth symbol
let logic_const name symbol = name_eq_to name logic symbol
let is_set name = plth_const name "Set"
let is_el name = plth_const name "El"
let is_predicate name = plth_const name "predicate"
let is_function name = plth_const name "function"
let is_nil name = plth_const name "nil"
let is_cons name = plth_const name "cons"
let is_prf name = plth_const name "Prf"
let is_true name = plth_const name "true"
let is_false name = plth_const name "false"
let is_imp name = plth_const name "imp"
let is_and name = plth_const name "and"
let is_or name = plth_const name "or"
let is_neg name = plth_const name "not"
let is_eq name = plth_const name "eq"
let is_neq name = plth_const name "neq"
let is_forall name = plth_const name "forall"
let is_exists name = plth_const name "ex"
let is_and_intro name = logic_const name "conj"
let is_or_intro_r name = logic_const name "or_intro_r"
let is_or_intro_l name = logic_const name "or_intro_l"
let is_ex_intro name = logic_const name "ex_intro"
let is_false_elim name = logic_const name "false__ind"
let is_or_elim name = logic_const name "or_elim"
let is_ex_elim name = logic_const name "ex_elim"
let is_and_elim_l name = logic_const name "and_elim_l"
let is_and_elim_r name = logic_const name "and_elim_r"
let is_and_ind name = logic_const name "and_ind"
let is_and_ind_r name = logic_const name "and_ind_r"
let is_and_ind_l name = logic_const name "and_ind_l"
(*
let is_and_ind_l name = logic_const name "and_ind_l"
let is_and_ind_r name = logic_const name "and_ind_r"
*)

let is_eq_ind name = logic_const name "eq_ind"
let is_eq_ind_r name = logic_const name "eq_ind_r"
let is_eq_refl name = logic_const name "eq_refl"
let is_eq_sym name = logic_const name "eq_sym"
let is_eq_trans name = logic_const name "eq_trans"
let is_I name = plth_const name "I"

let rec parse_set_list predicate_name args =
  match args with
  | T.Const (_, cst) when is_nil cst -> []
  | T.App (T.Const (_, cst), T.Const (_, set), [ arg ]) when is_cons cst ->
      pair_string_of_name set :: parse_set_list predicate_name arg
  | _ -> failwith ("Error ill-formed predicate " ^ predicate_name ^ ".")

let rec parse_element name_assoc x =
  match x with
  | T.Const (_, cst) -> Ast.GlobalElementCst (pair_string_of_name cst)
  | T.App (T.Const (_, f), t, args) ->
      let function_name = pair_string_of_name f in
      let args = List.map (parse_element name_assoc) (t :: args) in
      Ast.FunctionCall (function_name, args)
  | T.DB (_, id, _) ->
      let var_name = B.string_of_ident id in
      Ast.ElementCst (List.assoc var_name name_assoc)
  | _ ->
      failwith
        "Error, an element is either a constant or the application of a symbol \
         function."

(* No need of the context since we suppose the Dedukti code typechecks. *)
let rec parse_proposition set_index name_assoc p =
  match p with
  | T.Const (_, cst) when is_true cst -> Ast.True
  | T.Const (_, cst) when is_false cst -> Ast.False
  | T.Const (_, cst) -> Ast.GlobalProposition (pair_string_of_name cst)
  | T.DB (_, id, _) ->
      let var_name = B.string_of_ident id in
      Ast.PropositionCst (List.assoc var_name name_assoc)
  | T.App (T.Const (_, cst), t1, [ t2 ]) when is_imp cst ->
      Ast.Implication
        ( parse_proposition set_index name_assoc t1,
          parse_proposition set_index name_assoc t2 )
  | T.App (T.Const (_, cst), t1, [ t2 ]) when is_and cst ->
      Ast.Conjonction
        ( parse_proposition set_index name_assoc t1,
          parse_proposition set_index name_assoc t2 )
  | T.App (T.Const (_, cst), t1, [ t2 ]) when is_or cst ->
      Ast.Disjonction
        ( parse_proposition set_index name_assoc t1,
          parse_proposition set_index name_assoc t2 )
  | T.App (T.Const (_, cst), t, []) when is_neg cst ->
      Ast.Negation (parse_proposition set_index name_assoc t)
  | T.App (T.Const (_, cst), T.Const (_, set), [ t1; t2 ]) when is_eq cst ->
      Ast.Equality
        ( pair_string_of_name set,
          parse_element name_assoc t1,
          parse_element name_assoc t2 )
  | T.App (T.Const (_, cst), T.Const (_, set), [ t1; t2 ]) when is_neq cst ->
      Ast.NotEquality
        ( pair_string_of_name set,
          parse_element name_assoc t1,
          parse_element name_assoc t2 )
  | T.App (T.Const (_, cst), T.Const (_, set), [ T.Lam (_, id, _, t) ])
    when is_forall cst ->
      let set = pair_string_of_name set in
      let id = B.string_of_ident id in
      let elname, set_index = get_new_name set set_index in
      let name_assoc = (id, elname) :: List.remove_assoc id name_assoc in
      Ast.Forall (set, elname, parse_proposition set_index name_assoc t)
  | T.App (T.Const (_, cst), T.Const (_, set), [ T.Lam (_, id, _, t) ])
    when is_exists cst ->
      let set = pair_string_of_name set in
      let id = B.string_of_ident id in
      let elname, set_index = get_new_name set set_index in
      let name_assoc = (id, elname) :: List.remove_assoc id name_assoc in
      Ast.Exists (set, elname, parse_proposition set_index name_assoc t)
  | T.App (T.Const (_, f), t, args) ->
      let predicate_name = pair_string_of_name f in
      let args = List.map (parse_element name_assoc) (t :: args) in
      Ast.PredicateCall (predicate_name, args)
  | _ -> failwith "The following term is not a proposition.\n"

exception ParsingError of string

let rec parse_predicate_definition set_index name_assoc te =
  match te with
  | T.Lam (_, id, Some (T.App (T.Const (_, cst), T.Const (_, set), _)), t)
    when is_el cst ->
      let set = pair_string_of_name set in
      let id = B.string_of_ident id in
      let elname, set_index = get_new_name set set_index in
      let name_assoc = (id, elname) :: List.remove_assoc id name_assoc in
      let args, t = parse_predicate_definition set_index name_assoc t in
      ((elname, set) :: args, t)
  | t -> ([], parse_proposition set_index name_assoc t)

let rec parse_function_definition set_index name_assoc te =
  match te with
  | T.Lam (_, id, Some (T.App (T.Const (_, cst), T.Const (_, set), _)), t)
    when is_el cst ->
      let set = pair_string_of_name set in
      let id = B.string_of_ident id in
      let elname, set_index = get_new_name set set_index in
      let name_assoc = (id, elname) :: List.remove_assoc id name_assoc in
      let args, t = parse_function_definition set_index name_assoc t in
      ((elname, set) :: args, t)
  | t -> ([], parse_element name_assoc t)

let rec parse_proof set_index name_assoc p ctx locals =
  match p with
  | T.Const (_, cst) when is_I cst -> (Ast.T, Ast.True)
  | T.Const (_, cst) -> (
      let var_name = pair_string_of_name cst in
      match List.assoc_opt var_name ctx with
      | None ->
          failwith (Printf.sprintf "%s not in context" (string_of_name cst))
      | Some (Ast.HypothesisC p) -> (Ast.GlobalAssumption var_name, p)
      | _ ->
          failwith
            (Printf.sprintf "%s not a proposition in the context"
               (string_of_name cst)))
  | T.DB (_, id, _) -> (
      let var_name = List.assoc (B.string_of_ident id) name_assoc in
      match List.assoc_opt var_name locals with
      | None -> failwith (Printf.sprintf "%s not in context" var_name)
      | Some (Ast.HypothesisC p) -> (Ast.Assumption var_name, p)
      | _ ->
          failwith
            (Printf.sprintf "%s not a proposition in the context" var_name))
  | T.Lam (_, id, Some (T.App (T.Const (_, cst), T.Const (_, set), [])), t)
    when is_el cst ->
      let id = B.string_of_ident id in
      let set_name = pair_string_of_name set in
      let elname, set_index = get_new_name set_name set_index in
      let name_assoc = (id, elname) :: List.remove_assoc id name_assoc in
      let locals =
        (elname, Ast.ElementC set_name) :: List.remove_assoc elname locals
      in
      let prf, p = parse_proof set_index name_assoc t ctx locals in
      let pred = (set_name, elname, p) in
      (Ast.ForallIntro (pred, prf), Ast.Forall pred)
  | T.Lam (_, id, Some (T.App (T.Const (_, cst), statement, [])), t)
    when is_prf cst ->
      let id = B.string_of_ident id in
      let prop_name, set_index = get_new_name ("", "H") set_index in
      let name_assoc = (id, prop_name) :: List.remove_assoc id name_assoc in
      let statement = parse_proposition set_index name_assoc statement in
      let locals = (prop_name, Ast.HypothesisC statement) :: locals in
      let prf, p = parse_proof set_index name_assoc t ctx locals in
      (Ast.ImplIntro (prop_name, statement, prf), Ast.Implication (statement, p))
  | T.App (T.Const (_, cst), a, b :: aprf :: bprf :: rest) when is_and_intro cst
    ->
      let a = parse_proposition set_index name_assoc a in
      let b = parse_proposition set_index name_assoc b in
      let aprf, _ = parse_proof set_index name_assoc aprf ctx locals in
      let bprf, _ = parse_proof set_index name_assoc bprf ctx locals in
      parse_proof_with_other_args set_index name_assoc
        (Ast.AndIntro (a, b, aprf, bprf))
        (Ast.Conjonction (a, b))
        ctx locals rest
  | T.App (T.Const (_, cst), b, a :: bprf :: rest) when is_or_intro_l cst ->
      let a = parse_proposition set_index name_assoc a in
      let b = parse_proposition set_index name_assoc b in
      let prf, _ = parse_proof set_index name_assoc bprf ctx locals in
      parse_proof_with_other_args set_index name_assoc
        (Ast.OrIntroL (a, b, prf))
        (Ast.Disjonction (a, b))
        ctx locals rest
  | T.App (T.Const (_, cst), b, a :: aprf :: rest) when is_or_intro_r cst ->
      let a = parse_proposition set_index name_assoc a in
      let b = parse_proposition set_index name_assoc b in
      let prf, _ = parse_proof set_index name_assoc aprf ctx locals in
      parse_proof_with_other_args set_index name_assoc
        (Ast.OrIntroR (a, b, prf))
        (Ast.Disjonction (a, b))
        ctx locals rest
  | T.App
      ( T.Const (_, cst),
        T.Const (_, set),
        T.Lam (_, x, _, predicate) :: wit :: proof_ex :: rest )
    when is_ex_intro cst ->
      let id = B.string_of_ident x in
      let set_name = pair_string_of_name set in
      let elname, set_index = get_new_name set_name set_index in
      let name_assoc = (id, elname) :: List.remove_assoc id name_assoc in
      let p = parse_proposition set_index name_assoc predicate in
      let wit = parse_element name_assoc wit in
      let prf, _ = parse_proof set_index name_assoc proof_ex ctx locals in
      let pred = (set_name, elname, p) in
      parse_proof_with_other_args set_index name_assoc
        (Ast.ExIntro (pred, wit, prf))
        (Ast.Exists pred) ctx locals rest
  | T.App (T.Const (_, cst), p1, proof_false :: rest) when is_false_elim cst ->
      let prf, _ = parse_proof set_index name_assoc proof_false ctx locals in
      let p = parse_proposition set_index name_assoc p1 in
      parse_proof_with_other_args set_index name_assoc (Ast.FalseElim prf) p ctx
        locals rest
  | T.App (T.Const (_, cst), p1, p2 :: p :: proof_p :: proof_and :: rest)
    when is_and_ind cst ->
      let p1 = parse_proposition set_index name_assoc p1 in
      let p2 = parse_proposition set_index name_assoc p2 in
      let p = parse_proposition set_index name_assoc p in
      let proof_and, _ =
        parse_proof set_index name_assoc proof_and ctx locals
      in
      let h1_name, set_index = get_new_name ("", "H") set_index in
      let h2_name, set_index = get_new_name ("", "H") set_index in
      let proof_p =
        match proof_p with
        | T.Lam (_, h1, _, T.Lam (_, h2, _, proof_p)) ->
            let h1 = B.string_of_ident h1 in
            let h2 = B.string_of_ident h2 in
            let name_assoc = (h1, h1_name) :: List.remove_assoc h1 name_assoc in
            let name_assoc = (h2, h2_name) :: List.remove_assoc h2 name_assoc in
            fst (parse_proof set_index name_assoc proof_p ctx locals)
        | _ ->
            let proof_p, _ =
              parse_proof set_index name_assoc proof_p ctx locals
            in
            let newprop, _ = get_new_name ("", "H") set_index in
            Ast.Cut
              ( Ast.Implication (p1, Ast.Implication (p2, p)),
                proof_p,
                newprop,
                Ast.Apply
                  ( newprop,
                    [
                      Ast.TProof (Ast.Assumption h1_name);
                      Ast.TProof (Ast.Assumption h2_name);
                    ] ) )
      in
      parse_proof_with_other_args set_index name_assoc
        (Ast.AndInd (h1_name, p1, h2_name, p2, proof_and, p, proof_p))
        p ctx locals rest
  | T.App (T.Const (_, cst), p, q :: r :: proof_r :: proof_and :: rest)
    when is_and_ind_r cst ->
      let p = parse_proposition set_index name_assoc p in
      let q = parse_proposition set_index name_assoc q in
      let r = parse_proposition set_index name_assoc r in
      let hname, set_index = get_new_name ("", "H") set_index in
      let proof_and, _ =
        parse_proof set_index name_assoc proof_and ctx locals
      in
      let proof_r =
        match proof_r with
        | T.Lam (_, h, _, proof_r) ->
            let h = B.string_of_ident h in
            let name_assoc = (h, hname) :: List.remove_assoc h name_assoc in
            fst (parse_proof set_index name_assoc proof_r ctx locals)
        | _ ->
            let proof_r, _ =
              parse_proof set_index name_assoc proof_r ctx locals
            in
            let newprop, _ = get_new_name ("", "H") set_index in
            Ast.Cut
              ( Ast.Implication (q, r),
                proof_r,
                newprop,
                Ast.Apply (newprop, [ Ast.TProof (Ast.Assumption hname) ]) )
      in
      parse_proof_with_other_args set_index name_assoc
        (Ast.AndIndRight (p, hname, q, proof_and, r, proof_r))
        r ctx locals rest
  | T.App (T.Const (_, cst), p, q :: r :: proof_r :: proof_and :: rest)
    when is_and_ind_l cst ->
      let p = parse_proposition set_index name_assoc p in
      let q = parse_proposition set_index name_assoc q in
      let r = parse_proposition set_index name_assoc r in
      let hname, set_index = get_new_name ("", "H") set_index in
      let proof_and, _ =
        parse_proof set_index name_assoc proof_and ctx locals
      in
      let proof_r =
        match proof_r with
        | T.Lam (_, h, _, proof_r) ->
            let h = B.string_of_ident h in
            let name_assoc = (h, hname) :: List.remove_assoc h name_assoc in
            fst (parse_proof set_index name_assoc proof_r ctx locals)
        | _ ->
            let proof_r, _ =
              parse_proof set_index name_assoc proof_r ctx locals
            in
            let newprop, _ = get_new_name ("", "H") set_index in
            Ast.Cut
              ( Ast.Implication (p, r),
                proof_r,
                newprop,
                Ast.Apply (newprop, [ Ast.TProof (Ast.Assumption hname) ]) )
      in
      parse_proof_with_other_args set_index name_assoc
        (Ast.AndIndLeft (hname, p, q, proof_and, r, proof_r))
        r ctx locals rest
  | T.App (T.Const (_, cst), p, q :: proof :: rest) when is_and_elim_l cst ->
      let p = parse_proposition set_index name_assoc p in
      let q = parse_proposition set_index name_assoc q in
      let proof, _ = parse_proof set_index name_assoc proof ctx locals in
      parse_proof_with_other_args set_index name_assoc
        (Ast.AndElimLeft (p, q, proof))
        p ctx locals rest
  | T.App (T.Const (_, cst), p, q :: proof :: rest) when is_and_elim_r cst ->
      let p = parse_proposition set_index name_assoc p in
      let q = parse_proposition set_index name_assoc q in
      let proof, _ = parse_proof set_index name_assoc proof ctx locals in
      parse_proof_with_other_args set_index name_assoc
        (Ast.AndElimRight (p, q, proof))
        q ctx locals rest
  | T.App (T.Const (_, cst), p1, p2 :: p :: proof1 :: proof2 :: proof_or :: rest)
    when is_or_elim cst ->
      let h1_name, set_index = get_new_name ("", "H") set_index in
      let h2_name, set_index = get_new_name ("", "H") set_index in
      let p1 = parse_proposition set_index name_assoc p1 in
      let p2 = parse_proposition set_index name_assoc p2 in
      let p = parse_proposition set_index name_assoc p in
      let proof1 =
        match proof1 with
        | T.Lam (_, h1, _, proof1) ->
            let h1 = B.string_of_ident h1 in
            let name_assoc = (h1, h1_name) :: List.remove_assoc h1 name_assoc in
            fst (parse_proof set_index name_assoc proof1 ctx locals)
        | _ ->
            let proof1, _ =
              parse_proof set_index name_assoc proof1 ctx locals
            in
            let newprop, _ = get_new_name ("", "H") set_index in
            Ast.Cut
              ( Ast.Implication (p1, p),
                proof1,
                newprop,
                Ast.Apply (newprop, [ Ast.TProof (Ast.Assumption h1_name) ]) )
      in
      let proof2 =
        match proof2 with
        | T.Lam (_, h2, _, proof2) ->
            let h2 = B.string_of_ident h2 in
            let name_assoc = (h2, h2_name) :: List.remove_assoc h2 name_assoc in
            fst (parse_proof set_index name_assoc proof2 ctx locals)
        | _ ->
            let proof2, _ =
              parse_proof set_index name_assoc proof2 ctx locals
            in
            let newprop, _ = get_new_name ("", "H") set_index in
            Ast.Cut
              ( Ast.Implication (p2, p),
                proof2,
                newprop,
                Ast.Apply (newprop, [ Ast.TProof (Ast.Assumption h2_name) ]) )
      in
      let proof_or, _ = parse_proof set_index name_assoc proof_or ctx locals in
      parse_proof_with_other_args set_index name_assoc
        (Ast.OrInd (p1, p2, p, h1_name, proof1, h2_name, proof2, proof_or))
        p ctx locals rest
  (* forall wit, setn, h(predicate wit) => proofp *)
  | T.App
      ( T.Const (_, cst),
        T.Const (_, setn),
        T.Lam (_, x, _, predicate) :: p :: proof_p :: proof_ex :: rest )
    when is_ex_elim cst ->
      let set = pair_string_of_name setn in
      let x = B.string_of_ident x in
      let xname, set_index = get_new_name set set_index in
      let name_assoc1 = (x, xname) :: List.remove_assoc x name_assoc in
      let pred = parse_proposition set_index name_assoc1 predicate in
      let wit_name, set_index = get_new_name ("", "H") set_index in
      let h_name, set_index = get_new_name ("", "H") set_index in
      let p = parse_proposition set_index name_assoc p in
      let proof_ex, _ = parse_proof set_index name_assoc proof_ex ctx locals in
      let proof_p =
        match proof_p with
        | T.Lam (_, wit, _, T.Lam (_, h, _, proof_p)) ->
            let wit = B.string_of_ident wit in
            let name_assoc =
              (wit, wit_name) :: List.remove_assoc wit name_assoc
            in
            let h = B.string_of_ident h in
            let name_assoc = (h, h_name) :: List.remove_assoc h name_assoc in
            fst (parse_proof set_index name_assoc proof_p ctx locals)
        | _ ->
            let proof_p, _ =
              parse_proof set_index name_assoc proof_p ctx locals
            in
            let newprop, _ = get_new_name ("", "H") set_index in
            let pred =
              ( set,
                wit_name,
                Ast.Implication
                  (instantiate xname pred (Ast.ElementCst wit_name), p) )
            in
            Ast.Cut
              ( Ast.Forall pred,
                proof_p,
                newprop,
                Ast.Apply
                  ( newprop,
                    [
                      Ast.TElement (Ast.ElementCst wit_name);
                      Ast.TProof (Ast.Assumption h_name);
                    ] ) )
      in
      parse_proof_with_other_args set_index name_assoc
        (Ast.ExInd ((set, xname, pred), p, proof_ex, wit_name, h_name, proof_p))
        p ctx locals rest
  | T.App
      ( T.Const (_, cst),
        T.Const (_, set_name),
        x :: T.Lam (_, h1, _, predicate) :: proof :: y :: proof_eq :: rest )
    when is_eq_ind cst ->
      let h1 = B.string_of_ident h1 in
      let h1name, set_index1 = get_new_name ("", "H") set_index in
      let name_assoc1 = (h1, h1name) :: List.remove_assoc h1 name_assoc in
      let pred = parse_proposition set_index1 name_assoc1 predicate in
      let set = pair_string_of_name set_name in
      let x = parse_element name_assoc x in
      let y = parse_element name_assoc y in
      let proof, p = parse_proof set_index name_assoc proof ctx locals in
      let proof_eq, _ = parse_proof set_index name_assoc proof_eq ctx locals in
      parse_proof_with_other_args set_index name_assoc
        (Ast.EqElim ((set, h1, pred), x, y, proof, proof_eq))
        p ctx locals rest
  | T.App
      ( T.Const (_, cst),
        T.Const (_, set_name),
        x :: T.Lam (_, h1, _, predicate) :: proof :: y :: proof_eq :: rest )
    when is_eq_ind_r cst ->
      let h1 = B.string_of_ident h1 in
      let h1name, set_index1 = get_new_name ("", "H") set_index in
      let name_assoc1 = (h1, h1name) :: List.remove_assoc h1 name_assoc in
      let pred = parse_proposition set_index1 name_assoc1 predicate in
      let set = pair_string_of_name set_name in
      let x = parse_element name_assoc x in
      let y = parse_element name_assoc y in
      let proof, p = parse_proof set_index name_assoc proof ctx locals in
      let proof_eq, _ = parse_proof set_index name_assoc proof_eq ctx locals in
      parse_proof_with_other_args set_index name_assoc
        (Ast.EqElimR ((set, h1, pred), x, y, proof, proof_eq))
        p ctx locals rest
  | T.App (T.Const (_, cst), T.Const (_, set_name), x :: rest)
    when is_eq_refl cst ->
      let set = pair_string_of_name set_name in
      let x = parse_element name_assoc x in
      parse_proof_with_other_args set_index name_assoc
        (Ast.EqRefl (set, x))
        (Ast.Equality (set, x, x))
        ctx locals rest
  | T.App (T.Const (_, cst), T.Const (_, set_name), x :: y :: proof_eq :: rest)
    when is_eq_sym cst ->
      let set = pair_string_of_name set_name in
      let x = parse_element name_assoc x in
      let y = parse_element name_assoc y in
      let proof_eq, _ = parse_proof set_index name_assoc proof_eq ctx locals in
      parse_proof_with_other_args set_index name_assoc
        (Ast.EqSym (set, x, y, proof_eq))
        (Ast.Equality (set, y, x))
        ctx locals rest
  | T.App
      ( T.Const (_, cst),
        T.Const (_, set_name),
        x :: y :: z :: proof_eq1 :: proof_eq2 :: rest )
    when is_eq_trans cst ->
      let set = pair_string_of_name set_name in
      let x = parse_element name_assoc x in
      let y = parse_element name_assoc y in
      let z = parse_element name_assoc z in
      let proof_eq1, _ =
        parse_proof set_index name_assoc proof_eq1 ctx locals
      in
      let proof_eq2, _ =
        parse_proof set_index name_assoc proof_eq2 ctx locals
      in
      parse_proof_with_other_args set_index name_assoc
        (Ast.EqTrans (set, x, y, z, proof_eq1, proof_eq2))
        (Ast.Equality (set, x, z))
        ctx locals rest
  | T.App (prf, arg, rest) -> (
      let prf, p = parse_proof set_index name_assoc prf ctx locals in
      match p with
      | Ast.Implication (p, q) when p = q ->
          let prf, p = parse_proof set_index name_assoc arg ctx locals in
          parse_proof_with_other_args set_index name_assoc prf p ctx locals rest
      | _ ->
          parse_proof_with_other_args set_index name_assoc prf p ctx locals
            (arg :: rest)
      (* Problème ici, pourquoi prendre une fonction en paramètre et pas juste une
         preuve de p => r. Pareil pour and_ind, ex_elim et or_elim.
      *)
      (**** DELETE
          | T.App(T.Const(_, cst), arg, rest) ->
            let th = pair_string_of_name cst in
            let p = begin match List.assoc_opt th ctx with
              | None -> failwith (Printf.sprintf "%s not in context" (string_of_name cst))
              | Some(Ast.HypothesisC(p)) -> p
              | _ -> failwith (Printf.sprintf "%s not a proposition in the context" (string_of_name cst))
            end in
            parse_th_proof_with_other_args set_index name_assoc th [] p ctx locals (arg::rest)

        | T.App(prf, arg, rest) ->
          let (prf, p) = parse_proof set_index name_assoc prf ctx locals in
          parse_proof_with_other_args set_index name_assoc prf p ctx locals (arg::rest)
          DELETE ****))
  | _ ->
      Printf.printf "Not yet implemented proof.\n";
      (Ast.T, Ast.True)
(* Now, we just have to deal with applications... *)
(* Should we authorize connectives uses without elimination rules? Or
   should we restrict their use in order to not have any proposition
   as objects?*)
(*
    For each connectives, there are two eliminations ways.
    The first one is the "correct" way. It uses the elimination symbol.
    the second one uses the reduction rules associated to the connective.
    
    For instance, we can either have the proof `and_elim args` or the 
    proof `(and_proof) args` where `and_proof` is the proof of a 
    conjunction.
    
    Then, when we parse some elements (applications and abstraction),
    we have to check if they correspond to some proofs used as a
    theorem.
  *)

and parse_proof_with_other_args set_index name_assoc prf prop ctx locals args =
  match (prop, args) with
  | _, [] -> (prf, prop)
  | Ast.Implication (p, q), r :: rest -> (
      match prf with
      | Ast.Apply (th, l) ->
          let prfp, _ = parse_proof set_index name_assoc r ctx locals in
          let newprop, set_index = get_new_name ("", "H") set_index in
          let prfresult, result =
            parse_proof_with_other_args set_index name_assoc
              (Ast.Apply
                 ( th,
                   List.rev (Ast.TProof (Ast.Assumption newprop) :: List.rev l)
                 ))
              q ctx locals rest
          in
          (Ast.Cut (p, prfp, newprop, prfresult), result)
      | Ast.ApplyTheorem (th, l) ->
          let prfp, _ = parse_proof set_index name_assoc r ctx locals in
          let newprop, set_index = get_new_name ("", "H") set_index in
          let prfresult, result =
            parse_proof_with_other_args set_index name_assoc
              (Ast.ApplyTheorem
                 ( th,
                   List.rev (Ast.TProof (Ast.Assumption newprop) :: List.rev l)
                 ))
              q ctx locals rest
          in
          (Ast.Cut (p, prfp, newprop, prfresult), result)
      | _ ->
          let newprop, set_index = get_new_name ("", "H") set_index in
          let prfresult, result =
            parse_proof_with_other_args set_index name_assoc
              (Ast.Apply (newprop, []))
              prop ctx locals args
          in
          (Ast.Cut (Ast.Implication (p, q), prf, newprop, prfresult), result))
  | Ast.Forall pred, r :: rest -> (
      let x = parse_element name_assoc r in
      let _, id, p = pred in
      match prf with
      | Ast.Apply (th, l) ->
          parse_proof_with_other_args set_index name_assoc
            (Ast.Apply (th, List.rev (Ast.TElement x :: List.rev l)))
            (instantiate id p x) ctx locals rest
      | Ast.ApplyTheorem (th, l) ->
          parse_proof_with_other_args set_index name_assoc
            (Ast.ApplyTheorem (th, List.rev (Ast.TElement x :: List.rev l)))
            (instantiate id p x) ctx locals rest
      | _ ->
          let newprop, set_index = get_new_name ("", "H") set_index in
          let prfresult, result =
            parse_proof_with_other_args set_index name_assoc
              (Ast.Apply (newprop, []))
              prop ctx locals args
          in
          (Ast.Cut (Ast.Forall pred, prf, newprop, prfresult), result))
  | Ast.False, prop :: rest ->
      let prop = parse_proposition set_index name_assoc prop in
      let _, prop =
        parse_proof_with_other_args set_index name_assoc Ast.T prop ctx locals
          rest
      in
      (Ast.FalseElim prf, prop)
  | Ast.Conjonction (p1, p2), p :: prfp :: rest ->
      let h1_name, set_index = get_new_name ("", "H") set_index in
      let h2_name, set_index = get_new_name ("", "H") set_index in
      let p = parse_proposition set_index name_assoc p in
      let proof_p =
        match prfp with
        | T.Lam (_, h1, _, T.Lam (_, h2, _, proof_p)) ->
            let h1 = B.string_of_ident h1 in
            let h2 = B.string_of_ident h2 in
            let name_assoc = (h1, h1_name) :: List.remove_assoc h1 name_assoc in
            let name_assoc = (h2, h2_name) :: List.remove_assoc h2 name_assoc in
            fst (parse_proof set_index name_assoc proof_p ctx locals)
        | _ ->
            let proof_p, _ = parse_proof set_index name_assoc prfp ctx locals in
            let newprop, _ = get_new_name ("", "H") set_index in
            Ast.Cut
              ( Ast.Implication (p1, Ast.Implication (p2, p)),
                proof_p,
                newprop,
                Ast.Apply
                  ( newprop,
                    [
                      Ast.TProof (Ast.Assumption h1_name);
                      Ast.TProof (Ast.Assumption h2_name);
                    ] ) )
      in
      parse_proof_with_other_args set_index name_assoc
        (Ast.AndInd (h1_name, p1, h2_name, p2, prf, p, proof_p))
        p ctx locals rest
  | Ast.Conjonction (p1, p2), [ p ] ->
      let p = parse_proposition set_index name_assoc p in
      let h_name, set_index = get_new_name ("", "H") set_index in
      let h1_name, set_index = get_new_name ("", "H") set_index in
      let h2_name, set_index = get_new_name ("", "H") set_index in
      let newprop, _ = get_new_name ("", "H") set_index in
      let proof_p =
        Ast.ImplIntro
          ( h_name,
            Ast.Implication (p1, Ast.Implication (p2, p)),
            Ast.Apply
              ( newprop,
                [
                  Ast.TProof (Ast.Assumption h1_name);
                  Ast.TProof (Ast.Assumption h2_name);
                ] ) )
      in
      ( Ast.AndInd (h1_name, p1, h2_name, p2, prf, p, proof_p),
        Ast.Implication (Ast.Implication (p1, Ast.Implication (p2, p)), p) )
  | Ast.Equality (set, x, y), T.Lam (_, z, _, predicate) :: prf_x :: rest ->
      let id = B.string_of_ident z in
      let p = parse_proposition set_index name_assoc predicate in
      let pred = (set, id, p) in
      let prf_x, _ = parse_proof set_index name_assoc prf_x ctx locals in
      let prf_y = Ast.EqElim (pred, x, y, prf_x, prf) in
      parse_proof_with_other_args set_index name_assoc prf_y
        (instantiate id p y) ctx locals rest
  (*
(x = y) (P x) (P y)

cut x = y as H
  - H
  - cut (P x) as H
      + proof 
      + apply (H rest)  
*)
  (*TODO HERE *)
  (* Le cas où pas de prf_x = prouver P(a) => P(b) *)
  | Ast.Equality (set, x, y), [ T.Lam (_, z, _, predicate) ] ->
      let id = B.string_of_ident z in
      let p = parse_proposition set_index name_assoc predicate in
      let pred = (set, id, p) in
      let px = instantiate id p x in
      let py = instantiate id p y in
      let impl = Ast.Implication (px, py) in
      ( Ast.ImplIntro ("H", px, Ast.EqElim (pred, x, y, Ast.Assumption "H", prf)),
        impl )
  (*
    Had to manage other type of propositions, only, propositional variables/constants
    could not be used to proof another propositions.     
  *)
  | _ ->
      let _ = Printf.printf "%s\n" (Coq.coq_string_of_prop prop) in
      failwith "booh, not yet implemented"

and replace_el id el t =
  match el with
  | Ast.ElementCst x when id = x -> t
  | Ast.FunctionCall (f, l) ->
      Ast.FunctionCall (f, List.map (fun el -> replace_el id el t) l)
  | _ -> el

and instantiate (id : string) (p : Ast.proposition) (t : Ast.element) =
  match p with
  | Ast.Implication (p, q) ->
      Ast.Implication (instantiate id p t, instantiate id q t)
  | Ast.Conjonction (p, q) ->
      Ast.Conjonction (instantiate id p t, instantiate id q t)
  | Ast.Disjonction (p, q) ->
      Ast.Disjonction (instantiate id p t, instantiate id q t)
  | Ast.Negation p -> Ast.Negation (instantiate id p t)
  | Ast.Equality (set, x, y) ->
      Ast.Equality (set, replace_el id x t, replace_el id y t)
  | Ast.PredicateCall (f, l) ->
      Ast.PredicateCall (f, List.map (fun el -> replace_el id el t) l)
  | Forall (set, y, p) when id <> y -> Forall (set, y, instantiate id p t)
  | Exists (set, y, p) when id <> y -> Exists (set, y, instantiate id p t)
  | _ -> p

let parse_basic_declaration name decl =
  match decl with
  | T.Const (_, cst) when is_set cst -> (Ast.Set, Ast.SetC)
  | T.App (T.Const (_, cst), T.Const (_, set), []) when is_el cst ->
      let set = pair_string_of_name set in
      (Ast.Element set, Ast.ElementC set)
  | T.App (T.Const (_, cst), args, []) when is_predicate cst ->
      let args = parse_set_list name args in
      (Ast.PredicateSymbol args, Ast.PredicateC args)
  | T.App (T.Const (_, cst), args, [ T.Const (_, return) ]) when is_function cst
    ->
      let args = parse_set_list name args in
      let ret_type = pair_string_of_name return in
      (Ast.FunctionSymbol (args, ret_type), Ast.FunctionC (args, ret_type))
  | T.App (T.Const (_, cst), statement, []) when is_prf cst ->
      let statement = parse_proposition [] [] statement in
      (Ast.Axiom statement, Ast.HypothesisC statement)
  | _ ->
      raise
        (ParsingError
           "We can only declare sets, elements, predicates, functions and \
            poofs (axioms).")

let parse_basic_definition ty te ctx =
  match ty with
  | T.App (T.Const (_, cst), _, []) when is_predicate cst ->
      let args, te = parse_predicate_definition [] [] te in
      let args_type = List.map snd args in
      (Ast.Predicate (args, te), Ast.PredicateC args_type)
  | T.App (T.Const (_, cst), _, [ ret ]) when is_function cst ->
      let args, te = parse_function_definition [] [] te in
      let ret_type =
        match ret with
        | T.Const (_, cst) -> pair_string_of_name cst
        | _ -> failwith "Return type of a function should be a set."
      in
      let args_type = List.map snd args in
      (Ast.Function (args, ret_type, te), Ast.FunctionC (args_type, ret_type))
  | T.App (T.Const (_, cst), proposition, []) when is_prf cst ->
      let _ = (parse_proposition [] [], proposition) in
      let proof, prop = parse_proof [] [] te ctx [] in
      (Ast.Theorem (prop, proof), Ast.HypothesisC prop)
  | _ -> failwith "Error, we can only define functions, predicate and theorems."

let parse_entry mname ctx e =
  match e with
  | E.Decl (_, id, _, _, decl) ->
      let name = B.string_of_ident id in
      (*let _ = Printf.printf "Parsing declaration %s.%s...\n" mname name in *)
      let e, ce = parse_basic_declaration name decl in
      (*let _ = Printf.printf "Declaration %s parsed\n" name in *)
      (((mname, name), e), ((mname, name), ce))
  | E.Def (_, id, _, _, Some ty, te) ->
      let name = B.string_of_ident id in
      (* let _ = Printf.printf "Parsing definition %s...\n" name in *)
      let e, ce = parse_basic_definition ty te ctx in
      (* let _ = Printf.printf "Definition %s parsed\n" name in  *)
      (((mname, name), e), ((mname, name), ce))
  | _ ->
      raise
        (ParsingError
           "Error, can only translate definitions and declarations, rewrite \
            rules and commands are not accepted.")

(*let _ = begin match el with
    | Ast.AxiomDecl(_, p) -> Printf.printf "It is the following axiom: %s.\n" (Coq.string_of_coq_prop (Coq.translate_proposition p))
    | Ast.SetDecl(_) -> Printf.printf "It is a set.\n"
    | Ast.PredicateDecl(_, _) -> Printf.printf "It is a predicate.\n"
    | Ast.FunctionDecl(_, _, _) -> Printf.printf "It is a function.\n"
    | Ast.ElementDecl(_, set) -> Printf.printf "It is an element of %s.%s.\n" (fst set) (snd set)
    | _ -> Printf.printf "\n"
  end in

  let _ = begin match el with
  | Ast.TheoremDef(_, p, _) -> Printf.printf "It is the following theorem: %s.\n" (Coq.string_of_coq_prop (Coq.translate_proposition p))
  | Ast.PredicateDef(_, _, p) -> Printf.printf "It is the following predicate: %s.\n" (Coq.string_of_coq_prop (Coq.translate_proposition p))
  | Ast.FunctionDef(_, _, _, t) -> Printf.printf "It is the following function: %s.\n" (Coq.string_of_coq_element (Coq.translate_element t))
  | _ -> Printf.printf "\n"
  end in *)

(*

let is_const_eq_to c t =
  match t with
  | T.Const(_, cst) -> 
    let var_name = B.string_of_ident @@ B.id cst in
    let md_name = B.string_of_mident @@ B.md cst in
    md_name = "plth" && var_name = c 
  | _ -> false

  let is_nnpp t =
    match t with
    | T.Const(_, cst) -> 
      let var_name = B.string_of_ident @@ B.id cst in
      let md_name = B.string_of_mident @@ B.md cst in
      md_name = "euclidean__tactics" && var_name = "NNPP" 
    | _ -> false

    
let is_const_logic_eq_to c t =
    match t with
    | T.Const(_, cst) -> 
      let var_name = B.string_of_ident @@ B.id cst in
      let md_name = B.string_of_mident @@ B.md cst in
      md_name = "logic" && var_name = c 
    | _ -> false

let separate_const t =
  match t with
  | T.Const(_, cst) -> 
  let var_name = B.string_of_ident @@ B.id cst in
  let md_name = B.string_of_mident @@ B.md cst in
  (md_name, var_name) 
  | _ -> failwith "BOOM separate_const"


  let separate_const_best cst =
    let var_name = B.string_of_ident @@ B.id cst in
    let md_name = B.string_of_mident @@ B.md cst in
    (md_name, var_name)

let rec parse_element x = match x with
| T.Const (_, _) -> 
  let var_name = separate_const x in
  Ast.ElementCst(var_name)
| T.App (f, t, args) ->
  let function_name = separate_const f in 
  let first_arg = parse_element t in
  let args = List.map parse_element args in
  Ast.FunctionCall(function_name, first_arg::args)
| T.DB (_, id, _) ->
  let var_name =  B.string_of_ident id in
  Ast.ElementCst("", var_name)
| T.Lam (_, _, _, _) -> failwith "Je refuse"
| _ -> failwith "BOOM parse_element"




let rec compute_predicate predicate_name args = match args with
  | T.Const (_, _)(* when is_const_eq_to "nil" args*) -> []
  | T.App (t1, set, [arg]) when is_const_eq_to "cons" t1 -> 
    let (mod_name, set_name) = separate_const set in
    (mod_name, set_name)::(compute_predicate predicate_name arg)
  | _ -> failwith ("Error ill-formed predicate " ^ predicate_name ^ ".")


let rec compute_proof prf = 
match prf with
(*| T.Const (_, _) when is_const_eq_to "true" prf -> 
  Ast.True
| T.Const (_, _) when is_const_eq_to "false" prf -> 
  Ast.False*)
| T.Const (_, cst) ->
  let var_name = B.string_of_ident @@ B.id cst in
  Ast.Hypothesis(var_name)
| T.DB (_, id, _) ->
    let var_name =  B.string_of_ident id in
    Ast.Hypothesis(var_name)
| T.Lam(_, id, Some(T.App(el, T.Const(_, set), [])), t) when is_const_eq_to "El" el ->
  let id = B.string_of_ident id in
  let set_name = separate_const_best set in
  Ast.ForallIntro(id, set_name, compute_proof t)
| T.Lam(_, id, Some(T.App(prf, statement, [])), t) when is_const_eq_to "Prf" prf ->
    let id = B.string_of_ident id in
    let statement = parse_proposition statement in
    Ast.ImplIntro(id, statement, compute_proof t)
(* ICI À MODIFIER POUR REMETTRE LES RÈGLES D'INTRODUCTION DU ET/OU ET TOUT *)
| T.App(T.Lam(_, id, Some(T.App(_, statement, [])), t), statement_prf, []) ->
      let hypothesis_name = B.string_of_ident id in
      let statement = parse_proposition statement in
      let global_proof = compute_proof t in
      let statement_proof = compute_proof statement_prf in
      Ast.Cut(statement, hypothesis_name, statement_proof, global_proof)
| T.App (cst, t1, [t2]) when is_const_eq_to "imp" cst ->
        Ast.Implication(parse_proposition t1, parse_proposition t2)
| T.App (cst, t1, [t2]) when is_const_eq_to "and" cst ->
        Ast.Conjonction(parse_proposition t1, parse_proposition t2)
| T.App (cst, t1, [t2]) when is_const_eq_to "or" cst ->
        Ast.Disjonction(parse_proposition t1, parse_proposition t2)
| T.App (cst, T.Const(_, set), [t1; t2]) when is_const_eq_to "eq" cst ->
       Ast.Equality(separate_const_best set, parse_element t1, parse_element t2)
| T.App (cst, t, []) when is_const_eq_to "not" cst ->
        Ast.Negation(parse_element t)
| T.App(th, p1, [p2; p; T.Lam(_, h1, _, T.Lam(_, h2, _, proof_p)); proof_and]) when is_const_logic_eq_to "and__ind" th->
    let h1_name = B.string_of_ident h1 in
    let h2_name = B.string_of_ident h2 in 
    Ast.AndElim(
      parse_proposition p1, 
      parse_proposition p2, 
      parse_proposition p, 
      h1_name, 
      h2_name, 
      compute_proof proof_and,
      compute_proof proof_p
    )
| T.App(th, p1, [proof_false]) when is_const_logic_eq_to "false__ind" th->
      Ast.FalseElim(
        parse_proposition p1,
        compute_proof proof_false
      )
| T.App(th, p1, [p2; p; T.Lam(_, h1, _, proof1); T.Lam(_, h2, _, proof2); proof_or]) when is_const_logic_eq_to "or__ind" th->
      let h1_name = B.string_of_ident h1 in
      let h2_name = B.string_of_ident h2 in 
      Ast.OrElim(
        parse_proposition p1, 
        parse_proposition p2, 
        parse_proposition p, 
        h1_name,
        compute_proof proof1, 
        h2_name, 
        compute_proof proof2,
        compute_proof proof_or
      )
| T.App(th, T.Const(_, set_name), x::T.Lam(_, h1, _, predicate)::proof::y::proof_eq::args) when is_const_logic_eq_to "eq__ind" th->
  Ast.EqElim(
    separate_const_best set_name, 
    B.string_of_ident h1, 
    parse_proposition predicate, 
    parse_element x,
    parse_element y,
    compute_proof proof, 
    compute_proof proof_eq,
    List.map compute_proof args
  )
  | T.App(th, T.Const(_, set_name), x::T.Lam(_, h1, _, predicate)::proof::y::proof_eq::args) when is_const_logic_eq_to "eq__ind__r" th->
    Ast.EqElimR(
      separate_const_best set_name, 
      B.string_of_ident h1, 
      parse_proposition predicate, 
      parse_element x,
      parse_element y,
      compute_proof proof, 
      compute_proof proof_eq,
      List.map compute_proof args
    )
  (*| T.App(th, T.Const(_, set_name), x::T.Lam(_, h1, _, predicate)::proof::y::proof_eq::[args]) when is_const_logic_eq_to "eq__ind" th->
    Ast.Cut(
      parse_proposition predicate (* remplacer h1 par x*),
      B.string_of_ident h1,
      Ast.EqElim(
      separate_const_best set_name, 
      B.string_of_ident h1, 
      parse_proposition predicate, 
      parse_element x,
      parse_element y,
      (compute_proof proof),
      compute_proof proof_eq
    ),
    compute_proof args
    )
    | T.App(th, T.Const(_, set_name), x::T.Lam(_, h1, _, predicate)::proof::y::proof_eq::_) when is_const_logic_eq_to "eq__ind__r" th->
      Ast.EqElimR(
        separate_const_best set_name, 
        B.string_of_ident h1, 
        parse_proposition predicate, 
        parse_element x,
        parse_element y,
        compute_proof proof, 
        compute_proof proof_eq
      )
    (*TODO CORRECTLY *)
| T.App(th, T.Const(_, _), [_; T.Lam(_, _, _, _);_;_;_;_]) when is_const_logic_eq_to "eq__ind" th->
    failwith "OOO"*)

| T.App(th, T.Const(_, setn), [T.Lam(_, x, _,predicate); p; T.Lam(_, wit, _, T.Lam(_, h, _, proof_p)); proof_ex]) when is_const_logic_eq_to "ex__ind" th->
      let h_name = B.string_of_ident h in
      let x_name = B.string_of_ident x in
      let wit_name = B.string_of_ident wit in
      Ast.ExElim(
        x_name, 
        separate_const_best setn, 
        parse_proposition predicate, 
        parse_proposition p, 
        wit_name, 
        h_name,
        compute_proof proof_p,
        compute_proof proof_ex
      )
      
| T.App(th, b, [a; bprf]) when is_const_logic_eq_to "or__introl" th->
    Ast.OrIntroL(
      parse_proposition a,
      parse_proposition b,
      compute_proof bprf
    )
| T.App(th, b, [a; aprf]) when is_const_logic_eq_to "or__intror" th->
      Ast.OrIntroR(
        parse_proposition a,
        parse_proposition b,
        compute_proof aprf
      )
| T.App(th, a, [b; aprf; bprf]) when is_const_logic_eq_to "conj" th->
  Ast.AndIntro(
    parse_proposition a,
    parse_proposition b,
    compute_proof aprf,
    compute_proof bprf
  )
| T.App(th, T.Const(_, setn), [T.Lam(_, x, _,predicate); wit; proof_ex]) when is_const_logic_eq_to "ex__intro" th->
    let x_name = B.string_of_ident x in
    let set_name = separate_const_best setn in
    Ast.ExIntro(
      set_name, 
      x_name, 
      parse_proposition predicate, 
      parse_proposition wit,
      compute_proof proof_ex
    )
  | T.App(th, p, prf::args) when is_nnpp th->
      Ast.NNPP(
        parse_proposition p,
        compute_proof prf,
        List.map compute_proof args
      )
   (* | T.App (cst, T.Const(_, set), [T.Lam(_, id, _, t)]) when is_const_eq_to "forall" cst ->
      let x = B.string_of_ident id in
      Ast.Forall(separate_const_best set, x, parse_proposition t)
    | T.App (cst, T.Const(_, set), [T.Lam(_, id, _, t)]) when is_const_eq_to "ex" cst ->
      let x = B.string_of_ident id in
      Ast.Exists(separate_const_best set, x, parse_proposition t)
    | T.App (cst, t1, [t2]) when is_const_eq_to "imp" cst ->
      Ast.Implication(parse_proposition t1, parse_proposition t2)
    | T.App (cst, t1, [t2]) when is_const_eq_to "and" cst ->
      Ast.Conjonction(parse_proposition t1, parse_proposition t2)
    | T.App (cst, t1, [t2]) when is_const_eq_to "or" cst ->
      Ast.Disjonction(parse_proposition t1, parse_proposition t2)
    | T.App (cst, T.Const(_, set), [t1; t2]) when is_const_eq_to "eq" cst ->
     Ast.Equality(separate_const_best set, parse_element t1, parse_element t2)
    | T.App (T.Const(_, predicate), t, args) ->
      let predicate_name = separate_const_best predicate in
      let first_arg = parse_element t in
      let args = List.map parse_element args in
      Ast.PredicateCall(predicate_name, first_arg::args) *)

| T.App(T.Const(_, th), arg, args) ->
    let th_name = separate_const_best th in
    let args = List.map compute_proof (arg::args) in
    Ast.Apply(th_name, args)
| T.App(T.DB (_, id, _), arg, args) -> (* apply in *)
    let th_name = B.string_of_ident id in
    let args = List.map compute_proof (arg::args) in
    Ast.Apply(("", th_name), args)

| _ ->  failwith "NOPE compute_proof!!!"
  
let compute_type te name = match te with
  | T.Const(_, _) when is_const_eq_to "Set" te ->
    Ast.Set(name)
  | T.App (cst, T.Const (_, set), []) when is_const_eq_to "El" cst ->
    let set_name = separate_const_best set in
    Ast.Element(name, set_name)
  | T.App (cst, args, []) when is_const_eq_to "predicate" cst ->
      Ast.Predicate(name, compute_predicate name args)   
  | T.App (cst, args, [T.Const(_, ret)]) when is_const_eq_to "function" cst ->
      let return_type =  B.string_of_ident @@ B.id ret in
      let args_type = compute_predicate name args in
      Ast.Function(name, args_type, return_type)   
  | T.App(c, ty, _) when is_const_eq_to "Prf" c ->
    Ast.Axiom(name, parse_proposition ty)
  | _ -> failwith "Element is neither a Set nor an Element of a set nor a predicate nor a Prf."
*)

(*

f H1 H2 H3

f: P1 -> P2 -> p3 -> P4

  

*)

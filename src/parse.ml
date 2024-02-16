module T = Kernel.Term
module B = Kernel.Basic
module E = Parsers.Entry

let get_new_name (set : string * string) (set_index : (char * int) list) =
  let set = String.get (snd set) 0 in
  match List.assoc_opt set set_index with
  (* | None ->
         (Printf.sprintf "%s%d" (snd set) 0, (set, 1) :: set_index)
     | Some i ->
         ( Printf.sprintf "%s%d" (snd set) i,
           (set, i + 1) :: List.remove_assoc set set_index )
  *)
  | None -> (Printf.sprintf "%c%d" set 0, (set, 1) :: set_index)
  | Some i ->
      ( Printf.sprintf "%c%d" set i,
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
let is_nnpp name = plth_const name "nnpp"
let is_and_intro name = logic_const name "and_intro"
let is_or_intro_r name = logic_const name "or_intro_right"
let is_or_intro_l name = logic_const name "or_intro_left"
let is_ex_intro name = logic_const name "ex_intro"
let is_false_elim name = logic_const name "false_elim"
let is_or_elim name = logic_const name "or_elim"
let is_ex_elim name = logic_const name "ex_elim"
let is_and_elim_l name = logic_const name "and_elim_left"
let is_and_elim_r name = logic_const name "and_elim_right"
let is_and_ind name = logic_const name "and_ind"
let is_and_ind_r name = logic_const name "and_ind_right"
let is_and_ind_l name = logic_const name "and_ind_left"
(*
let is_and_ind_l name = logic_const name "and_ind_l"
let is_and_ind_r name = logic_const name "and_ind_r"
*)

let is_eq_ind name = logic_const name "eq__ind"
let is_eq_ind_r name = logic_const name "eq__ind__r"
let is_eq_refl name = logic_const name "eq__refl"
let is_eq_sym name = logic_const name "eq__sym"
let is_eq_trans name = logic_const name "eq__trans"
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
      Ast.Variable (List.assoc var_name name_assoc)
  | _ ->
      failwith
        "Error, an element is either a constant or the application of a symbol \
         function."


let rec parse_proposition set_index name_assoc p =
  match p with
  | T.Const (_, cst) when is_true cst -> Ast.True
  | T.Const (_, cst) when is_false cst -> Ast.False
  | T.Const (_, cst) -> Ast.GlobalProposition (pair_string_of_name cst)
  (*| T.DB (_, id, _) ->
      let var_name = B.string_of_ident id in
      Ast.PropositionCst (List.assoc var_name name_assoc) *)
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
          failwith
            (Printf.sprintf "%s not in global context" (string_of_name cst))
      | Some (Ast.HypothesisC p) -> (Ast.GlobalAssumption var_name, p)
      | _ ->
          failwith
            (Printf.sprintf "%s not a proposition in the global context"
               (string_of_name cst)))
  | T.DB (_, id, _) -> (
      let var_name = B.string_of_ident id in
      let new_name = List.assoc var_name name_assoc in
      match List.assoc_opt var_name locals with
      | None ->
          failwith
            (Printf.sprintf "%s (%s) not in local context" var_name new_name)
      | Some (Ast.HypothesisC p) -> (Ast.Assumption new_name, p)
      | _ ->
          failwith
            (Printf.sprintf "%s not a proposition in the local context" var_name)
      )
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
      let prop_name, set_index = get_new_name ("", "Himp") set_index in
      let name_assoc = (id, prop_name) :: List.remove_assoc id name_assoc in
      let statement = parse_proposition set_index name_assoc statement in
      let locals = (id, Ast.HypothesisC statement) :: locals in
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
  | T.App (T.Const (_, cst), prop, proof :: rest) when is_nnpp cst ->
      let prf, _ = parse_proof set_index name_assoc proof ctx locals in
      let p = parse_proposition set_index name_assoc prop in
      parse_proof_with_other_args set_index name_assoc
        (Ast.NNPP (p, prf))
        p ctx locals rest
  | T.App (T.Const (_, cst), p1, p2 :: p :: proof_p :: proof_and :: rest)
    when is_and_ind cst ->
      let p1 = parse_proposition set_index name_assoc p1 in
      let p2 = parse_proposition set_index name_assoc p2 in
      let p = parse_proposition set_index name_assoc p in
      let proof_and, _ =
        parse_proof set_index name_assoc proof_and ctx locals
      in
      let h1_name, set_index = get_new_name ("", "Handp") set_index in
      let h2_name, set_index = get_new_name ("", "Handq") set_index in
      let proof_p =
        match proof_p with
        | T.Lam (_, h1, _, T.Lam (_, h2, _, proof_p)) ->
            let h1 = B.string_of_ident h1 in
            let h2 = B.string_of_ident h2 in
            let name_assoc = (h1, h1_name) :: List.remove_assoc h1 name_assoc in
            let name_assoc = (h2, h2_name) :: List.remove_assoc h2 name_assoc in
            let locals = (h1, Ast.HypothesisC p1) :: locals in
            let locals = (h2, Ast.HypothesisC p2) :: locals in
            let result =
              fst (parse_proof set_index name_assoc proof_p ctx locals)
            in
            result
        | _ ->
            let proof_p, _ =
              parse_proof set_index name_assoc proof_p ctx locals
            in
            let newprop, _ = get_new_name ("", "Hand") set_index in
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
      let hname, set_index = get_new_name ("", "Handq") set_index in
      let proof_and, _ =
        parse_proof set_index name_assoc proof_and ctx locals
      in
      let proof_r =
        match proof_r with
        | T.Lam (_, h, _, proof_r) ->
            let h = B.string_of_ident h in
            let name_assoc = (h, hname) :: List.remove_assoc h name_assoc in
            let locals = (h, Ast.HypothesisC q) :: locals in
            fst (parse_proof set_index name_assoc proof_r ctx locals)
        | _ ->
            let proof_r, _ =
              parse_proof set_index name_assoc proof_r ctx locals
            in
            let newprop, _ = get_new_name ("", "Hand") set_index in
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
      let hname, set_index = get_new_name ("", "Handp") set_index in
      let proof_and, _ =
        parse_proof set_index name_assoc proof_and ctx locals
      in
      let proof_r =
        match proof_r with
        | T.Lam (_, h, _, proof_r) ->
            let h = B.string_of_ident h in
            let name_assoc = (h, hname) :: List.remove_assoc h name_assoc in
            let locals = (h, Ast.HypothesisC p) :: locals in
            fst (parse_proof set_index name_assoc proof_r ctx locals)
        | _ ->
            let proof_r, _ =
              parse_proof set_index name_assoc proof_r ctx locals
            in
            let newprop, _ = get_new_name ("", "Hand") set_index in
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
      let h1_name, set_index = get_new_name ("", "Horp") set_index in
      let h2_name, set_index = get_new_name ("", "Horq") set_index in
      let p1 = parse_proposition set_index name_assoc p1 in
      let p2 = parse_proposition set_index name_assoc p2 in
      let p = parse_proposition set_index name_assoc p in
      let proof1 =
        match proof1 with
        | T.Lam (_, h1, _, proof1) ->
            let h1 = B.string_of_ident h1 in
            let name_assoc1 =
              (h1, h1_name) :: List.remove_assoc h1 name_assoc
            in
            let locals1 = (h1, Ast.HypothesisC p1) :: locals in
            fst (parse_proof set_index name_assoc1 proof1 ctx locals1)
        | _ ->
            let proof1, _ =
              parse_proof set_index name_assoc proof1 ctx locals
            in
            let newprop, _ = get_new_name ("", "Hor") set_index in
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
            let name_assoc2 =
              (h2, h2_name) :: List.remove_assoc h2 name_assoc
            in
            let locals2 = (h2, Ast.HypothesisC p2) :: locals in
            fst (parse_proof set_index name_assoc2 proof2 ctx locals2)
        | _ ->
            let proof2, _ =
              parse_proof set_index name_assoc proof2 ctx locals
            in
            let newprop, _ = get_new_name ("", "Hor") set_index in
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
      let wit_name, set_index = get_new_name ("", snd set) set_index in
      let h_name, set_index = get_new_name ("", "Hexp") set_index in
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
            let locals =
              ( h,
                Ast.HypothesisC
                  (Ast.instantiate xname pred (Ast.ElementCst wit_name)) )
              :: locals
            in
            fst (parse_proof set_index name_assoc proof_p ctx locals)
        | _ ->
            let proof_p, _ =
              parse_proof set_index name_assoc proof_p ctx locals
            in
            let newprop, _ = get_new_name ("", "Hex") set_index in
            let pred =
              ( set,
                wit_name,
                Ast.Implication
                  (Ast.instantiate xname pred (Ast.ElementCst wit_name), p) )
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
      let heq, set_index = get_new_name ("", "Heq") set_index in
      let hprf, set_index = get_new_name ("", "Heqp") set_index in
      let proof, _ = parse_proof set_index name_assoc proof ctx locals in
      let proof_eq, _ = parse_proof set_index name_assoc proof_eq ctx locals in
      parse_proof_with_other_args set_index name_assoc
        (Ast.EqElim ((set, h1name, pred), x, y, hprf, proof, heq, proof_eq))
        (Ast.instantiate h1name pred y)
        ctx locals rest
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
      let heq, set_index = get_new_name ("", "Heq") set_index in
      let hprf, set_index = get_new_name ("", "Heqp") set_index in
      let proof, _ = parse_proof set_index name_assoc proof ctx locals in
      let proof_eq, _ = parse_proof set_index name_assoc proof_eq ctx locals in
      parse_proof_with_other_args set_index name_assoc
        (Ast.EqElimR ((set, h1name, pred), x, y, hprf, proof, heq, proof_eq))
        (Ast.instantiate h1name pred y)
        ctx locals rest
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
  | T.App
      (T.Lam (_, id, Some (T.App (_, statement, [])), prf), statement_prf, args)
    ->
      let statement = parse_proposition set_index name_assoc statement in
      let id = B.string_of_ident id in
      let statement_proof, _ =
      parse_proof set_index name_assoc statement_prf ctx locals
      in begin match statement_proof with
        (*| Ast.Assumption(v) -> 
          let name_assoc1 = (id, v) :: List.remove_assoc id name_assoc in
          let locals1 = (id, Ast.HypothesisC statement) :: locals in
          let prf, result = parse_proof set_index name_assoc1 prf ctx locals1 in
          parse_proof_with_other_args set_index name_assoc prf result ctx locals args  
        (* Do the same with global assumption *)     
            *)
        | _ -> 
          let hname, set_index1 = get_new_name ("", "Hcut") set_index in
          let name_assoc1 = (id, hname) :: List.remove_assoc id name_assoc in
          let locals1 = (id, Ast.HypothesisC statement) :: locals in
          let prf, result = parse_proof set_index1 name_assoc1 prf ctx locals1 in
          parse_proof_with_other_args set_index name_assoc
          (Ast.Cut (statement, statement_proof, hname, prf))
          result ctx locals args
    end
  | T.App (prf, arg, rest) ->
      let prf, p = parse_proof set_index name_assoc prf ctx locals in
      (*begin match p with
        | Ast.Implication (p, q) when p = q ->
            let prf, p = parse_proof set_index name_assoc arg ctx locals in
            parse_proof_with_other_args set_index name_assoc prf p ctx locals rest
        | _ ->*)
      parse_proof_with_other_args set_index name_assoc prf p ctx locals
        (arg :: rest)
      (*end *)

      (*
      Cut (p1 -> p2, apply ...,)   
    *)

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
          DELETE ****)
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
          let newprop, set_index = get_new_name ("", "G") set_index in
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
          let newprop, set_index = get_new_name ("", "G") set_index in
          let prfresult, result =
            parse_proof_with_other_args set_index name_assoc
              (Ast.ApplyTheorem
                 ( th,
                   List.rev (Ast.TProof (Ast.Assumption newprop) :: List.rev l)
                 ))
              q ctx locals rest
          in
          (Ast.Cut (p, prfp, newprop, prfresult), result)
      | Ast.GlobalAssumption th ->
          let prfp, _ = parse_proof set_index name_assoc r ctx locals in
          let newprop, set_index = get_new_name ("", "G") set_index in
          let prfresult, result =
            parse_proof_with_other_args set_index name_assoc
              (Ast.ApplyTheorem (th, [ Ast.TProof (Ast.Assumption newprop) ]))
              q ctx locals rest
          in
          (Ast.Cut (p, prfp, newprop, prfresult), result)
      | Ast.Assumption h ->
          let prfp, _ = parse_proof set_index name_assoc r ctx locals in
          let newprop, set_index = get_new_name ("", "G") set_index in
          let prfresult, result =
            parse_proof_with_other_args set_index name_assoc
              (Ast.Apply (h, [ Ast.TProof (Ast.Assumption newprop) ]))
              q ctx locals rest
          in
          (Ast.Cut (p, prfp, newprop, prfresult), result)
      | _ ->
          Printf.printf "Là";
          let newprop, set_index = get_new_name ("", "G") set_index in
          let prfresult, result =
            parse_proof_with_other_args set_index name_assoc
              (Ast.Apply (newprop, []))
              prop ctx locals args
          in
          (Ast.Cut (Ast.Implication (p, q), prf, newprop, prfresult), result))
  | Ast.Forall pred, r :: rest -> (
      let x =
        match parse_element name_assoc r with
        | Ast.Variable x -> Ast.ElementCst x
        | x -> x
      in
      let _, id, p = pred in
      (*Printf.printf "%s %s.\n" id (Coq.coq_string_of_prop p);
      Printf.printf "inst with %s => %s.\n"
        (Coq.string_of_coq_element (Coq.translate_element x))
        (Coq.coq_string_of_prop (Ast.instantiate id p x)); *)
      match prf with
      | Ast.Apply (th, l) ->
          parse_proof_with_other_args set_index name_assoc
            (Ast.Apply (th, List.rev (Ast.TElement x :: List.rev l)))
            (Ast.instantiate id p x) ctx locals rest
      | Ast.ApplyTheorem (th, l) ->
          parse_proof_with_other_args set_index name_assoc
            (Ast.ApplyTheorem (th, List.rev (Ast.TElement x :: List.rev l)))
            (Ast.instantiate id p x) ctx locals rest
      (* If (Global) Assumption, something to do here *)
      | Ast.GlobalAssumption th ->
          parse_proof_with_other_args set_index name_assoc
            (Ast.ApplyTheorem (th, [ Ast.TElement x ]))
            (Ast.instantiate id p x) ctx locals rest
      | Ast.Assumption h ->
          parse_proof_with_other_args set_index name_assoc
            (Ast.Apply (h, [ Ast.TElement x ]))
            (Ast.instantiate id p x) ctx locals rest
      | _ ->
          let newprop, set_index = get_new_name ("", "G") set_index in
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
      let h1_name, set_index = get_new_name ("", "Hargandp") set_index in
      let h2_name, set_index = get_new_name ("", "Hargandq") set_index in
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
            let newprop, _ = get_new_name ("", "Hargand") set_index in
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
      let h_name, set_index = get_new_name ("", "Harg") set_index in
      let h1_name, set_index = get_new_name ("", "Hargp") set_index in
      let h2_name, set_index = get_new_name ("", "Hargq") set_index in
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
      let heq, set_index = get_new_name ("", "H") set_index in
      let hprf, set_index = get_new_name ("", "H") set_index in
      let prf_x, _ = parse_proof set_index name_assoc prf_x ctx locals in
      let prf_y = Ast.EqElim (pred, x, y, hprf, prf_x, heq, prf) in
      parse_proof_with_other_args set_index name_assoc prf_y
        (Ast.instantiate id p y) ctx locals rest
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
      let px = Ast.instantiate id p x in
      let py = Ast.instantiate id p y in
      let heq, set_index = get_new_name ("", "H") set_index in
      let hprf, _ = get_new_name ("", "H") set_index in
      let impl = Ast.Implication (px, py) in
      ( Ast.ImplIntro
          ("H", px, Ast.EqElim (pred, x, y, hprf, Ast.Assumption "H", heq, prf)),
        impl )
  (*
    Had to manage other type of propositions, only, propositional variables/constants
    could not be used to proof another propositions.     
  *)
  | Ast.Negation p, r :: rest -> (
      match prf with
      | Ast.Apply (th, l) ->
          let prfp, _ = parse_proof set_index name_assoc r ctx locals in
          let newprop, set_index = get_new_name ("", "Hargneg") set_index in
          let prfresult, result =
            parse_proof_with_other_args set_index name_assoc
              (Ast.Apply
                 ( th,
                   List.rev (Ast.TProof (Ast.Assumption newprop) :: List.rev l)
                 ))
              Ast.False ctx locals rest
          in
          (Ast.Cut (p, prfp, newprop, prfresult), result)
      | Ast.ApplyTheorem (th, l) ->
          let prfp, _ = parse_proof set_index name_assoc r ctx locals in
          let newprop, set_index = get_new_name ("", "Hargneg") set_index in
          let prfresult, result =
            parse_proof_with_other_args set_index name_assoc
              (Ast.ApplyTheorem
                 ( th,
                   List.rev (Ast.TProof (Ast.Assumption newprop) :: List.rev l)
                 ))
              False ctx locals rest
          in
          (Ast.Cut (p, prfp, newprop, prfresult), result)
      | _ ->
          let newprop, set_index = get_new_name ("", "Hargneg") set_index in
          let prfresult, result =
            parse_proof_with_other_args set_index name_assoc
              (Ast.Apply (newprop, []))
              prop ctx locals args
          in
          (Ast.Cut (Ast.Negation p, prf, newprop, prfresult), result))
  | Ast.NotEquality (set, x, y), _ ->
      parse_proof_with_other_args set_index name_assoc prf
        (Ast.Negation (Ast.Equality (set, x, y)))
        ctx locals args
  | _ ->
      (*let _ = Printf.printf "%s\n" (Coq.coq_string_of_prop prop) in *)
      failwith "booh, not yet implemented"

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

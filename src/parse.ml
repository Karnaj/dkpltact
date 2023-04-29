module T = Kernel.Term
module B = Kernel.Basic
module E = Parsers.Entry


let id_name cst = B.string_of_ident @@ B.id cst
let md_name cst = B.string_of_mident @@ B.md cst

let pair_string_of_name name = (md_name name, id_name name)

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
let is_forall name = plth_const name "forall"
let is_exists name = plth_const name "ex"

let rec parse_set_list predicate_name args = match args with
  | T.Const (_, cst) when is_nil cst -> []
  | T.App (T.Const(_, cst), T.Const(_, set), [arg]) when is_cons cst -> 
    (pair_string_of_name set)::(parse_set_list predicate_name arg)
  | _ -> failwith ("Error ill-formed predicate " ^ predicate_name ^ ".")

let rec parse_element x = match x with
| T.Const (_, cst) -> 
  Ast.ElementCst(pair_string_of_name cst)
| T.App (T.Const(_, f), t, args) ->
  let function_name = pair_string_of_name f in
  let args = List.map parse_element (t::args) in
  Ast.FunctionCall(function_name, args)
| T.DB (_, id, _) ->
  let var_name =  B.string_of_ident id in
  Ast.ElementCst("", var_name)
| _ -> failwith "Error, an element is either a constant or the application of a symbol function."


(* No need of the context since we suppose the Dedukti code typechecks. *)
let rec parse_proposition p = match p with
  | T.Const (_, cst) when is_true cst -> 
      Ast.True
  | T.Const (_, cst) when is_false cst -> 
      Ast.False
  | T.Const (_, cst) -> 
      Ast.GlobalProposition(pair_string_of_name cst)
  | T.DB (_, id, _) ->
      let var_name =  B.string_of_ident id in
      Ast.PropositionCst(var_name) 
  | T.App (T.Const (_, cst), t1, [t2]) when is_imp cst ->
    Ast.Implication(parse_proposition t1, parse_proposition t2)
  | T.App (T.Const (_, cst), t1, [t2]) when is_and cst ->
    Ast.Conjonction(parse_proposition t1, parse_proposition t2)
  | T.App (T.Const (_, cst), t1, [t2]) when is_or cst ->
    Ast.Disjonction(parse_proposition t1, parse_proposition t2)
  | T.App (T.Const (_, cst), t, []) when is_neg cst ->
    Ast.Negation(parse_proposition t)
  | T.App (T.Const (_, cst), T.Const(_, set), [t1; t2]) when is_eq cst ->
    Ast.Equality(pair_string_of_name set, parse_element t1, parse_element t2)
  | T.App (T.Const(_, cst), T.Const(_, set), [T.Lam(_, id, _, t)]) when is_forall cst ->
      Ast.Forall(pair_string_of_name set, B.string_of_ident id, parse_proposition t)
  | T.App (T.Const(_, cst), T.Const(_, set), [T.Lam(_, id, _, t)]) when is_exists cst ->  
      Ast.Exists(pair_string_of_name set, B.string_of_ident id, parse_proposition t)
  | T.App (T.Const(_, f), t, args) ->
    let predicate_name = pair_string_of_name f in
    let args = List.map parse_element (t::args) in
    Ast.PredicateCall(predicate_name, args)
  | _  -> failwith "The following term is not a proposition.\n" 

exception ParsingError of string



let parse_proof p _ = match p with 
  | T.Const (_, cst) ->
    Ast.GlobalAssumption(pair_string_of_name cst)
  | T.DB (_, id, _) ->
    let var_name =  B.string_of_ident id in
    Ast.Assumption(var_name)
  | _ -> Printf.printf "Not yet implemented proof.\n"; Ast.T
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


let rec parse_predicate_definition te = match te with 
  | T.Lam(_, id, Some(T.App(T.Const(_, cst), T.Const(_, set), _)), t) when is_el cst -> 
      let (args, t) = parse_predicate_definition t in
      ((B.string_of_ident id, pair_string_of_name set)::args, t)
  | t -> ([], parse_proposition t)

let rec parse_function_definition te = match te with 
  | T.Lam(_, id, Some(T.App(T.Const(_, cst), T.Const(_, set), _)), t) when is_el cst -> 
      let (args, t) = parse_function_definition t in
      ((B.string_of_ident id, pair_string_of_name set)::args, t)
  | t -> ([], parse_element t)


let parse_basic_declaration name decl = match decl with 
  | T.Const(_, cst) when is_set cst -> 
      Ast.SetDecl(name)
  | T.App (T.Const(_, cst), T.Const (_, set), []) when is_el cst ->
      Ast.ElementDecl(name, pair_string_of_name set)
  | T.App (T.Const(_, cst), args, []) when is_predicate cst ->
      Ast.PredicateDecl(name, parse_set_list name args)
  | T.App (T.Const(_, cst), args, [T.Const(_, return)]) when is_function cst ->
      Ast.FunctionDecl(name, parse_set_list name args, pair_string_of_name return)
  | T.App (T.Const(_, cst), statement, []) when is_prf cst ->
      let statement = parse_proposition statement in
      Ast.AxiomDecl(name, statement)
  | _ -> 
    raise (ParsingError "We can only declare sets, elements, predicates, functions and poofs (axioms).")


let parse_basic_definition name ty te = match ty with
  | T.App (T.Const(_, cst), _, []) when is_predicate cst ->
      let args, te = parse_predicate_definition te in
      Ast.PredicateDef(name, args, te)
  | T.App (T.Const(_, cst), _, [ret]) when is_function cst ->
      let args, te = parse_function_definition te in
      let ret_type = begin match ret with
        | T.Const(_, cst) -> pair_string_of_name cst
        | _ -> failwith "Return type of a function should be a set."
      end in
      Ast.FunctionDef(name, args, ret_type, te)
  | T.App (T.Const(_, cst), proposition, []) when is_prf cst ->
      Ast.TheoremDef(name, parse_proposition proposition, parse_proof ty [])
  | _ -> 
    failwith "Error, we can only define functions, predicate and theorems."  

let parse_entry mname ctx e = match e with
  | E.Decl(_, id, _, _, decl) ->
      let name = B.string_of_ident id in
      (*let _ = Printf.printf "Parsing declaration %s...\n" name in *)
      let e = parse_basic_declaration name decl in
      let ctx = ((mname, name), e)::ctx in
      (*let _ = Printf.printf "Declaration %s parsed\n" name in *)
      (ctx, e)
  | E.Def(_, id, _, _, Some(ty), te) -> 
      let name = B.string_of_ident id in 
      let _ = Printf.printf "Parsing definition %s...\n" name in
      let e = parse_basic_definition name ty te in
      let _ = Printf.printf "Definition %s parsed\n" name in 
      let ctx = ((mname, name), e)::ctx in
      (ctx, e)
  | _ -> 
      raise (ParsingError "Error, can only translate definitions and declarations, rewrite rules and commands are not accepted.")  

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


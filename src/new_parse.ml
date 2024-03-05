module T = Kernel.Term
module B = Kernel.Basic
module E = Parsers.Entry

exception ParsingError of string

type local_hypothesis = (string * (Ast.proof * Ast.proposition)) list
type local_elements = (string * (Ast.element * Ast.set)) list
type set_index = (char * int) list
type parsing_context = set_index * local_hypothesis * local_elements
type context = parsing_context * Ast._global_context

let string_of_name name = fst name ^ "." ^ snd name
let new_parsing_context : parsing_context = ([], [], [])

let fresh_name (initial : char) (set_index : set_index) :
    Ast.variable * set_index =
  match List.assoc_opt initial set_index with
  | None ->
      let new_name = Printf.sprintf "%c%d" initial 0 in
      (new_name, (initial, 1) :: set_index)
  | Some i ->
      let new_name = Printf.sprintf "%c%d" initial i in
      (new_name, (initial, i + 1) :: List.remove_assoc initial set_index)

let fresh_local_hypothesis (c : context) : Ast.variable * context =
  let c, g = c in
  let set_index, hypothesis, elements = c in
  let id, set_index = fresh_name 'H' set_index in
  (id, ((set_index, hypothesis, elements), g))

let fresh_local_element (set : Ast.set) (c : context) : Ast.variable * context =
  let c, g = c in
  let set_index, hypothesis, elements = c in
  let id, set_index = fresh_name (String.get (snd set) 0) set_index in
  (id, ((set_index, hypothesis, elements), g))

let declare_local_hypothesis (id : string) (c : context) (p : Ast.proposition) :
    Ast.variable * context =
  let h, c = fresh_local_hypothesis c in
  let c, g = c in
  let set_index, hypothesis, elements = c in
  let hypothesis =
    (id, (Ast.Assumption h, p)) :: List.remove_assoc id hypothesis
  in
  (h, ((set_index, hypothesis, elements), g))

let declare_local_element (id : string) (c : context) (set : Ast.set) :
    Ast.variable * context =
  let x, c = fresh_local_element set c in
  let c, g = c in
  let set_index, hypothesis, elements = c in
  let elements = (id, (Ast.Variable x, set)) :: List.remove_assoc id elements in
  (x, ((set_index, hypothesis, elements), g))

let define_local_hypothesis (id : string) (c : context) (p : Ast.proposition)
    (prf : Ast.proof) : context =
  let c, g = c in
  let set_index, hypothesis, elements = c in
  let hypothesis = (id, (prf, p)) :: List.remove_assoc id hypothesis in
  ((set_index, hypothesis, elements), g)

let define_local_element (id : string) (c : context) (set : Ast.set)
    (x : Ast.element) : context =
  let c, g = c in
  let set_index, hypothesis, elements = c in
  let elements = (id, (x, set)) :: List.remove_assoc id elements in
  ((set_index, hypothesis, elements), g)

let get_local_hypothesis (id : string) (c : context) :
    Ast.proof * Ast.proposition =
  let c, _ = c in
  let _, hypothesis, _ = c in
  match List.assoc_opt id hypothesis with
  | None -> failwith (Printf.sprintf "No hypothesis %s in Δ." id)
  | Some p -> p

let get_local_element (id : string) (c : context) : Ast.element * Ast.set =
  let c, _ = c in
  let _, _, elements = c in
  match List.assoc_opt id elements with
  | None -> failwith (Printf.sprintf "No element %s in Δ." id)
  | Some x -> x

let get_global_element (dk_cst : string * string) (context : context) :
    Ast.set * Ast.element option =
  let _, globals = context in
  match List.assoc_opt dk_cst (Ast.global_elements globals) with
  | None ->
      failwith (Printf.sprintf "No element %s in Γ." (string_of_name dk_cst))
  | Some x -> x

let get_global_hypothesis (dk_cst : string * string) (context : context) :
    Ast.proposition =
  let _, globals = context in
  match List.assoc_opt dk_cst (Ast.global_hypothesis globals) with
  | None ->
      failwith (Printf.sprintf "No hypothesis %s in Γ." (string_of_name dk_cst))
  | Some x -> x

let get_global_function (dk_cst : string * string) (context : context) :
    (Ast.set list * Ast.set) * (Ast.variable list * Ast.element) option =
  let _, globals = context in
  match List.assoc_opt dk_cst (Ast.global_functions globals) with
  | None ->
      failwith (Printf.sprintf "No function %s in Γ." (string_of_name dk_cst))
  | Some x -> x

let get_global_predicate (dk_cst : string * string) (context : context) :
    Ast.set list * (Ast.variable list * Ast.proposition) option =
  let _, globals = context in
  match List.assoc_opt dk_cst (Ast.global_predicates globals) with
  | None ->
      failwith (Printf.sprintf "No predicate %s in Γ." (string_of_name dk_cst))
  | Some x -> x

let set_exist (dk_cst : string * string) (context : context) : bool =
  let _, globals = context in
  Ast.set_exist dk_cst globals

let rec unfold_proposition (p : Ast.proposition) (c : context) : Ast.proposition
    =
  let _, globals = c in
  match p with
  | GlobalProposition h -> unfold_proposition (Ast.PredicateCall (h, [])) c
  | PredicateCall (f, args) -> (
      match List.assoc_opt f (Ast.global_predicates globals) with
      | None -> failwith "todo best message"
      | Some (_, None) -> failwith "better message"
      | Some (_, Some (ids, prop)) ->
          unfold_proposition (instantiate_all ids prop args) c)
  | _ -> p

and instantiate_all (ids : Ast.variable list) (p : Ast.proposition)
    (args : Ast.element list) : Ast.proposition =
  let _ = (ids, args, p) in
  p (* TODO*)

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
let is_classic name = plth_const name "classic"
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
let is_eq_ind name = logic_const name "eq_ind"
let is_eq_ind_r name = logic_const name "eq_ind_r"
let is_eq_refl name = logic_const name "eq_refl"
let is_eq_sym name = logic_const name "eq_sym"
let is_eq_trans name = logic_const name "eq_trans"
let is_I name = plth_const name "I"

let rec parse_set_list context predicate_name args =
  match args with
  | T.Const (_, cst) when is_nil cst -> []
  | T.App (T.Const (_, cst), T.Const (_, set), [ arg ]) when is_cons cst -> (
      let dk_name = pair_string_of_name set in
      match set_exist dk_name context with
      | false ->
          failwith (Printf.sprintf "No set %s not in Γ." (string_of_name cst))
      | _ -> dk_name :: parse_set_list context predicate_name arg)
  | _ -> failwith ("Error ill-formed predicate " ^ predicate_name ^ ".")

let rec parse_element (context : context) (x : T.term) : Ast.element * Ast.name
    =
  match x with
  | T.Const (_, cst) ->
      let dk_name = pair_string_of_name cst in
      let set, _ = get_global_element dk_name context in
      (Ast.GlobalElementCst dk_name, set)
  | T.App (T.Const (_, f), t, args) ->
      let dk_name = pair_string_of_name f in
      let (fun_args_type, return), _ = get_global_function dk_name context in
      let args_with_type = List.map (parse_element context) (t :: args) in
      let args, args_type = List.split args_with_type in
      if List.equal (fun x y -> x = y) args_type fun_args_type then
        (Ast.FunctionCall (dk_name, args), return)
      else
        failwith
          (Printf.sprintf "Error function call %s with bad arguments."
             (string_of_name f))
  | T.DB (_, id, _) ->
      let dk_name = B.string_of_ident id in
      let x, set = get_local_element dk_name context in
      (x, set)
  | _ ->
      failwith
        "Error, an element is either a constant or the application of a symbol \
         function."

let rec parse_proposition (context : context) (p : T.term) : Ast.proposition =
  match p with
  | T.Const (_, cst) when is_true cst -> Ast.True
  | T.Const (_, cst) when is_false cst -> Ast.False
  | T.Const (_, cst) ->
      let dk_name = pair_string_of_name cst in
      (* replace by check_global_hypothesis **)
      let _ = get_global_hypothesis dk_name context in
      Ast.GlobalProposition dk_name
  | T.App (T.Const (_, cst), t1, [ t2 ]) when is_imp cst ->
      Ast.Implication
        (parse_proposition context t1, parse_proposition context t2)
  | T.App (T.Const (_, cst), t1, [ t2 ]) when is_and cst ->
      Ast.Conjonction
        (parse_proposition context t1, parse_proposition context t2)
  | T.App (T.Const (_, cst), t1, [ t2 ]) when is_or cst ->
      Ast.Disjonction
        (parse_proposition context t1, parse_proposition context t2)
  | T.App (T.Const (_, cst), t, []) when is_neg cst ->
      Ast.Negation (parse_proposition context t)
  | T.App (T.Const (_, cst), T.Const (_, set), [ t1; t2 ]) when is_eq cst ->
      Ast.Equality
        ( pair_string_of_name set,
          fst (parse_element context t1),
          fst (parse_element context t2) )
  | T.App (T.Const (_, cst), T.Const (_, set), [ t1; t2 ]) when is_neq cst ->
      Ast.NotEquality
        ( pair_string_of_name set,
          fst (parse_element context t1),
          fst (parse_element context t2) )
  | T.App (T.Const (_, cst), T.Const (_, set), [ T.Lam (_, id, _, t) ])
    when is_forall cst ->
      let set = pair_string_of_name set in
      let id = B.string_of_ident id in
      let id, context = declare_local_element id context set in
      Ast.Forall (set, id, parse_proposition context t)
  | T.App (T.Const (_, cst), T.Const (_, set), [ T.Lam (_, id, _, t) ])
    when is_exists cst ->
      let set = pair_string_of_name set in
      let id = B.string_of_ident id in
      let id, context = declare_local_element id context set in
      Ast.Exists (set, id, parse_proposition context t)
  | T.App (T.Const (_, f), t, args) ->
      let predicate_name = pair_string_of_name f in
      let predicate_args_type, _ =
        get_global_predicate predicate_name context
      in
      let args_with_type = List.map (parse_element context) (t :: args) in
      let args, args_type = List.split args_with_type in
      if List.equal (fun x y -> x = y) args_type predicate_args_type then
        Ast.PredicateCall (predicate_name, args)
      else
        failwith
          (Printf.sprintf "Error predicate call %s with bad arguments."
             (string_of_name f))
  | _ -> failwith "The following term is not a proposition.\n"

let rec parse_predicate_definition (context : context) (te : T.term) :
    (Ast.variable * Ast.name) list * Ast.proposition =
  match te with
  | T.Lam (_, id, Some (T.App (T.Const (_, cst), T.Const (_, set), _)), t)
    when is_el cst ->
      let set = pair_string_of_name set in
      let id = B.string_of_ident id in
      let id, context = declare_local_element id context set in
      let args, t = parse_predicate_definition context t in
      ((id, set) :: args, t)
  | t -> ([], parse_proposition context t)

let rec parse_function_definition (context : context) (te : T.term) :
    (Ast.variable * Ast.name) list * (Ast.element * Ast.name) =
  match te with
  | T.Lam (_, id, Some (T.App (T.Const (_, cst), T.Const (_, set), _)), t)
    when is_el cst ->
      let set = pair_string_of_name set in
      let id = B.string_of_ident id in
      let id, context = declare_local_element id context set in
      let args, t = parse_function_definition context t in
      ((id, set) :: args, t)
  | t -> ([], parse_element context t)

let rec parse_proof (context : context) (p : T.term) :
    Ast.proof * Ast.proposition =
  match p with
  | T.Const (_, cst) when is_I cst -> (Ast.T, Ast.True)
  | T.Const (_, cst) ->
      let dk_name = pair_string_of_name cst in
      let p = get_global_hypothesis dk_name context in
      (Ast.GlobalAssumption dk_name, p)
  | T.DB (_, id, _) ->
      let dk_name = B.string_of_ident id in
      get_local_hypothesis dk_name context
  | T.Lam (_, id, Some (T.App (T.Const (_, cst), T.Const (_, set), [])), prf)
    when is_el cst ->
      let id = B.string_of_ident id in
      let set = pair_string_of_name set in
      let id, context = declare_local_element id context set in
      let prf, p = parse_proof context prf in
      let abs = (set, id, p) in
      (Ast.ForallIntro (abs, prf), Ast.Forall abs)
  | T.Lam (_, id, Some (T.App (T.Const (_, cst), statement, [])), t)
    when is_prf cst ->
      let id = B.string_of_ident id in
      let statement = parse_proposition context statement in
      let id, context = declare_local_hypothesis id context statement in
      let prf, p = parse_proof context t in
      (Ast.ImplIntro (id, statement, prf), Ast.Implication (statement, p))
  | T.Lam (_, id, None, _) ->
      let id = B.string_of_ident id in
      failwith (Printf.sprintf "Here %s" id)
  | T.App (T.Const (_, cst), prop, proof :: rest) when is_nnpp cst ->
      let prf, _ = parse_proof context proof in
      let p = parse_proposition context prop in
      parse_application context (Ast.NNPP (p, prf)) p rest
  (*  nnpp p is a proof of ~~p -> p. *)
  | T.App (T.Const (_, cst), prop, rest) when is_classic cst ->
      let p = parse_proposition context prop in
      parse_application context (Ast.Classic p)
        (Ast.Disjonction (p, Ast.Negation p))
        rest
  | T.App (T.Const (_, cst), a, b :: aprf :: bprf :: rest) when is_and_intro cst
    ->
      let a = parse_proposition context a in
      let b = parse_proposition context b in
      let aprf, _ = parse_proof context aprf in
      let bprf, _ = parse_proof context bprf in
      parse_application context
        (Ast.AndIntro (a, b, aprf, bprf))
        (Ast.Conjonction (a, b))
        rest
  (* and_intro a b aprf is a proof of b -> a /\ b,
     and_intro a b is a proof of a -> b -> a /\ b.
     We cannot have fewer arguments. Indeed, and_intro a would be a proof of the proposition
     forall b, a -> b -> a /\ b, but this is not a term of predicate logic since it quantifies over
     propositions. It would be a correct term in a theory with propositions as types. *)
  | T.App (T.Const (_, cst), a, b :: aprf :: rest) when is_or_intro_l cst ->
      let a = parse_proposition context a in
      let b = parse_proposition context b in
      let aprf, _ = parse_proof context aprf in
      parse_application context
        (Ast.OrIntroL (a, b, aprf))
        (Ast.Disjonction (a, b))
        rest
  | T.App (T.Const (_, cst), a, b :: bprf :: rest) when is_or_intro_r cst ->
      let a = parse_proposition context a in
      let b = parse_proposition context b in
      let bprf, _ = parse_proof context bprf in
      parse_application context
        (Ast.OrIntroR (a, b, bprf))
        (Ast.Disjonction (a, b))
        rest
      (* or_intro_l a b is a proof of a -> a \/ b.
         or_intro_r a b is a proof of b -> a \/ b.
         Here again, fewer arguments requires a theory where Prop is a Set. *)
  | T.App
      ( T.Const (_, cst),
        T.Const (_, set),
        T.Lam (_, x, _, prop) :: wit :: proof_ex :: rest )
    when is_ex_intro cst ->
      let wit = fst (parse_element context wit) in
      let prf, _ = parse_proof context proof_ex in
      let id = B.string_of_ident x in
      let set = pair_string_of_name set in
      let id, pcontext = declare_local_element id context set in
      let p = parse_proposition pcontext prop in
      let abs = (set, id, p) in
      parse_application context
        (Ast.ExIntro (abs, wit, prf))
        (Ast.Exists abs) rest
      (* ex_intro set P x is a proof of P(x) -> ex x: set, P(x).
         ex_intro set P is a proof of forall x, P(x) -> ex x: set, P(x).
         Here, ex_intro set would be a proof of forall P: set -> Prop, forall x, P(x) -> ex x: set, P(x).
         However, this require the ability to quantify over predicates,
         hence a more expressive theory such as simple type theory. *)
  | T.App (T.Const (_, cst), p, proof_false :: rest) when is_false_elim cst ->
      let prf, _ = parse_proof context proof_false in
      let p = parse_proposition context p in
      parse_application context (Ast.FalseElim prf) p rest
      (* false_elim p is a proof of false -> p. *)
  | T.App (T.Const (_, cst), p1, p2 :: p :: proof_p :: proof_and :: rest)
    when is_and_ind cst ->
      parse_and_elim context p1 p2 p proof_p proof_and rest
      (* and_ind p q r prfr is a proof of p /\ q -> r.
         and_ind p q r is a proof of (p -> q -> r) -> (p /\ q) -> r. *)
  | T.App (T.Const (_, cst), p1, p2 :: p :: proof_p :: proof_and :: rest)
    when is_and_ind_l cst ->
      parse_and_elim_l context p1 p2 p proof_p proof_and rest
      (* and_ind_l p q r prfr is a proof of p /\ q -> r.
         and_ind_l p q r is a proof of (p -> r) -> (p /\ q) -> r. *)
  | T.App (T.Const (_, cst), p1, p2 :: p :: proof_p :: proof_and :: rest)
    when is_and_ind_r cst ->
      parse_and_elim_r context p1 p2 p proof_p proof_and rest
      (* and_ind_r p q r prfr is a proof of p /\ q -> r.
         and_ind_r p q r is a proof of (q -> r) -> (p /\ q) -> r. *)
  | T.App (T.Const (_, cst), p, q :: proof :: rest) when is_and_elim_l cst ->
      let p = parse_proposition context p in
      let q = parse_proposition context q in
      let proof, _ = parse_proof context proof in
      parse_application context (Ast.AndElimLeft (p, q, proof)) p rest
      (* and_elim_l p q is a proof of p /\ q -> p. *)
  | T.App (T.Const (_, cst), p, q :: proof :: rest) when is_and_elim_r cst ->
      let p = parse_proposition context p in
      let q = parse_proposition context q in
      let proof, _ = parse_proof context proof in
      parse_application context (Ast.AndElimRight (p, q, proof)) q rest
      (* and_elim_r p q is a proof of p /\ q -> p. *)
  | T.App (T.Const (_, cst), p1, p2 :: p :: proof1 :: proof2 :: proof_or :: rest)
    when is_or_elim cst ->
      parse_or_elim context p1 p2 p proof1 proof2 proof_or rest
      (* or_elim p q r prf1 prf2 is a proof of p \/ q -> r
         or_elim p q r prf1 is a proof of (q -> r) -> p \/ q -> r.
         or_elim p q r is a proof of (p -> r) -> (q -> r) -> p \/ q -> r. *)
  | T.App
      ( T.Const (_, cst),
        T.Const (_, setn),
        T.Lam (_, x, _, prop) :: p :: proof_p :: proof_ex :: rest )
    when is_ex_elim cst ->
      parse_ex_elim context setn x prop p proof_p proof_ex rest
  | T.App
      ( T.Const (_, cst),
        T.Const (_, set_name),
        x :: abs :: proof :: y :: proof_eq :: rest )
    when is_eq_ind cst ->
      let x, _ = parse_element context x in
      let y, _ = parse_element context y in
      let set = pair_string_of_name set_name in
      let proof, _ = parse_proof context proof in
      let proof_eq, _ = parse_proof context proof_eq in
      let h1, prop =
        match parse_predicate_definition context abs with
        | [ (h1, _) ], prop -> (h1, prop)
        | _ -> failwith "eq_ind waits for a predicate on one element."
      in
      let heq, context =
        match proof_eq with
        | Ast.Assumption h -> (h, context)
        | _ -> fresh_local_hypothesis context
      in
      let hprf, context =
        match proof with
        | Ast.Assumption h -> (h, context)
        | _ -> fresh_local_hypothesis context
      in
      parse_application context
        (Ast.EqElim ((set, h1, prop), x, y, hprf, proof, heq, proof_eq))
        (Ast.instantiate h1 prop y)
        rest
      (* eq_ind set x P prf y is a proof of x = y -> P(y).
         eq_ind set x P prf is a proof of forall y, x = y -> P(y).
         eq_ind set x P is a proof of P(x) -> forall y, x = y -> P(y). *)
  | T.App
      ( T.Const (_, cst),
        T.Const (_, set_name),
        x :: abs :: proof :: y :: proof_eq :: rest )
    when is_eq_ind_r cst ->
      let x, _ = parse_element context x in
      let y, _ = parse_element context y in
      let set = pair_string_of_name set_name in
      let proof, _ = parse_proof context proof in
      let proof_eq, _ = parse_proof context proof_eq in
      let h1, prop =
        match parse_predicate_definition context abs with
        | [ (h1, _) ], prop -> (h1, prop)
        | _ -> failwith "eq_ind waits for a predicate on one element."
      in
      let heq, context =
        match proof_eq with
        | Ast.Assumption h -> (h, context)
        | _ -> fresh_local_hypothesis context
      in
      let hprf, context =
        match proof with
        | Ast.Assumption h -> (h, context)
        | _ -> fresh_local_hypothesis context
      in
      parse_application context
        (Ast.EqElimR ((set, h1, prop), x, y, hprf, proof, heq, proof_eq))
        (Ast.instantiate h1 prop y)
        rest
      (* eq_ind_r set x P prf y is a proof of y = x -> P(y).
         eq_ind_r set x P prf is a proof of forall y, y = x -> P(y).
         eq_ind_r set x P is a proof of P(x) -> forall y, y = x -> P(y). *)
  | T.App (T.Const (_, cst), T.Const (_, set_name), x :: rest)
    when is_eq_refl cst ->
      let set = pair_string_of_name set_name in
      let x, _ = parse_element context x in
      parse_application context
        (Ast.EqRefl (set, x))
        (Ast.Equality (set, x, x))
        rest
      (* eq_refl set is a proof of forall x: set, x = x. *)
  | T.App (T.Const (_, cst), T.Const (_, set_name), x :: y :: proof_eq :: rest)
    when is_eq_sym cst ->
      let set = pair_string_of_name set_name in
      let x, _ = parse_element context x in
      let y, _ = parse_element context y in
      let proof_eq, _ = parse_proof context proof_eq in
      parse_application context
        (Ast.EqSym (set, x, y, proof_eq))
        (Ast.Equality (set, y, x))
        rest
      (* eq_sym set x y is a proof of x = y -> y = x.
         eq_sym set x is a proof of forall y: set, x = y -> y = x.
         eq_sym set is a proof of forall x y: set, x = y -> y = x. *)
  | T.App
      ( T.Const (_, cst),
        T.Const (_, set_name),
        x :: y :: z :: proof_eq1 :: proof_eq2 :: rest )
    when is_eq_trans cst ->
      let set = pair_string_of_name set_name in
      let x, _ = parse_element context x in
      let y, _ = parse_element context y in
      let z, _ = parse_element context z in
      let proof_eq1, _ = parse_proof context proof_eq1 in
      let proof_eq2, _ = parse_proof context proof_eq2 in
      parse_application context
        (Ast.EqTrans (set, x, y, z, proof_eq1, proof_eq2))
        (Ast.Equality (set, x, z))
        rest
      (* eq_trans set x y z proof1 is a proof of y = z -> x = z.
          eq_trans set x y z is a proof of x = y -> y = z -> x = z.
          eq_trans set x y is a proof of forall z: set, x = y -> y = z -> x = z.
          eq_trans set x is a proof of forall y z: set, x = y -> y = z -> x = z.
          eq_trans set is a proof of forall x y z: set, x = y -> y = z -> x = z. *)
  | T.App
      ( T.Const (_, cst),
        T.Const (_, setn),
        T.Lam (_, x, _, prop) :: p :: proof_p :: proof_ex :: rest )
    when is_ex_elim cst ->
      let _ = (setn, x, prop, p, proof_p, proof_ex, rest) in
      failwith "exixts todo"
  | T.App (prf, arg, rest) -> parse_app context prf (arg :: rest)
  | _ -> failwith "not a correct proof"

and parse_app (context : context) (prf : T.term) (args : T.term list) :
    Ast.rule * Ast.proposition =
  match (prf, args) with
  | ( T.Lam (_, id, Some (T.App (T.Const (_, cst), T.Const (_, set), [])), prf),
      x :: args )
    when is_el cst ->
      let id = B.string_of_ident id in
      let set = pair_string_of_name set in
      let x, _ = parse_element context x in
      let context = define_local_element id context set x in
      parse_app context prf args
  | ( T.Lam (_, id, Some (T.App (T.Const (_, cst), statement, [])), prf),
      prfp :: args )
    when is_prf cst -> (
      let id = B.string_of_ident id in
      let statement = parse_proposition context statement in
      let prfp, _ = parse_proof context prfp in
      match prfp with
      | Ast.Assumption _ | Ast.GlobalAssumption _ ->
          let context = define_local_hypothesis id context statement prfp in
          parse_app context prf args
      | _ ->
          let h, context = declare_local_hypothesis id context statement in
          let prf, ret = parse_app context prf args in
          (Ast.Cut (statement, prfp, h, prf), ret))
  | _ ->
      let prf, p = parse_proof context prf in
      parse_application context prf p args

and parse_application (context : context) (prf : Ast.proof)
    (p : Ast.proposition) (args : T.term list) : Ast.rule * Ast.proposition =
  let _ = (args, context) in
  (* Printf.printf "ere\n!"; *)
  match (p, args) with
  | _, [] -> (prf, p)
  | Ast.True, _ ->
      failwith "Cannot create proof by applying arguments to a proof of True."
  | Ast.Implication (_, _), _ | Ast.Forall _, _ -> (
      match prf with
      | Ast.Apply (th, l) ->
          parse_arguments context p args
            (fun l -> Ast.Apply (th, l))
            (List.rev l)
      | Ast.ApplyTheorem (th, l) ->
          parse_arguments context p args
            (fun l -> Ast.ApplyTheorem (th, l))
            (List.rev l)
      | Ast.Assumption th ->
          parse_arguments context p args (fun l -> Ast.Apply (th, l)) []
      | Ast.GlobalAssumption th ->
          parse_arguments context p args (fun l -> Ast.ApplyTheorem (th, l)) []
      | Ast.ImplIntro (id, _, proof) ->
          let _ = (id, proof) in
          failwith "IMPOSSIBLE"
      | Ast.ForallIntro ((_, id, prop), proof) ->
          let _ = (id, prop, proof) in
          failwith "Impossible"
          (* let t, args = (List.hd args, List.tl args) in
             let t, _ = parse_element context t in
             let x = begin match t with
               | Ast.Variable(x) -> Ast.ElementCst(x)
               | y -> y in
             let prop = Ast.instantiate id prop x in
             let proof = Ast.instantiate_in_proof id t proof in
             parse_application context proof prop args *)
      | _ -> (
          let h, context = fresh_local_hypothesis context in
          match p with
          | Ast.Implication (_, _) ->
              parse_arguments context p args
                (fun l -> Ast.Cut (p, prf, h, Ast.Apply (h, l)))
                []
          | _ ->
              parse_arguments context p args
                (fun l -> Ast.Cut (p, prf, h, Ast.Apply (h, l)))
                []))
  | Ast.False, p :: rest ->
      let p = parse_proposition context p in
      parse_application context (Ast.FalseElim prf) p rest
  | Ast.Negation p, args ->
      parse_application context prf (Ast.Implication (p, Ast.False)) args
  (* Here again, disjonction and conjonction could take less arguments. *)
  | Ast.Disjonction (p1, p2), q :: prf_p1_imp_q :: prf_p2_imp_q :: rest ->
      parse_or_elim_ context p1 p2
        (parse_proposition context q)
        prf_p1_imp_q prf_p2_imp_q prf rest
  | Ast.Disjonction _, _ ->
      failwith
        "We do noy yet parse disjonction proof applied to not enough arguments."
  | Ast.Conjonction (p1, p2), q :: prfimp :: rest ->
      parse_and_elim_ context p1 p2
        (parse_proposition context q)
        prfimp prf rest
  | Ast.Conjonction _, _ ->
      failwith
        "We do nor yet parse conjonction proof applied to not enough arguments."
  | Ast.Exists abs, p :: prf_imp :: rest ->
      parse_ex_elim_ context abs (parse_proposition context p) prf_imp prf rest
  | Ast.Exists _, _ ->
      failwith
        "We do noy yet parse exists proof applied to not enough arguments."
  | Ast.NotEquality (set, x, y), _ ->
      parse_application context prf
        (Ast.Negation (Ast.Equality (set, x, y)))
        args
  | Ast.PredicateCall (predicate_name, params), args ->
      (*begin match get_global_type predicate_name context with
          | None -> failwith "JJJJ"
          | _ -> failwithh "todo"
        end *)
      let _ = (predicate_name, params, args) in
      failwith "predicate todo"
  | Ast.GlobalProposition _, _ -> failwith "global propo todo"
  | Ast.Equality _, _ -> failwith "parse equality todo"

and parse_arguments (context : context) (p : Ast.proposition)
    (args : T.term list) (f : Ast.term list -> Ast.proof)
    (current_args : Ast.term list) : Ast.proof * Ast.proposition =
  match (p, args) with
  | Ast.Implication (p, q), prf :: rest -> (
      match fst (parse_proof context prf) with
      | Ast.Assumption h ->
          parse_arguments context q rest f
            (TProof (Ast.Assumption h) :: current_args)
      | Ast.GlobalAssumption h ->
          parse_arguments context q rest f
            (TProof (Ast.GlobalAssumption h) :: current_args)
      | prf ->
          let hp, context = fresh_local_hypothesis context in
          let prfret, ret =
            parse_arguments context q rest f
              (TProof (Ast.Assumption hp) :: current_args)
          in
          (Ast.Cut (p, prf, hp, prfret), ret))
  | Ast.Forall (_, id, p), x :: rest ->
      let x =
        match fst (parse_element context x) with
        | Ast.Variable x -> Ast.ElementCst x
        | y -> y
      in
      parse_arguments context (Ast.instantiate id p x) rest f
        (TElement x :: current_args)
  | _ -> parse_application context (f (List.rev current_args)) p args

and parse_or_elim (context : context) (p1 : T.term) (p2 : T.term) (p : T.term)
    (proof1 : T.term) (proof2 : T.term) (proof_or : T.term) (args : T.term list)
    =
  let p1 = parse_proposition context p1 in
  let p2 = parse_proposition context p2 in
  let p = parse_proposition context p in
  let proof_or, _ = parse_proof context proof_or in
  parse_or_elim_ context p1 p2 p proof1 proof2 proof_or args

and parse_or_elim_ (context : context) (p1 : Ast.proposition)
    (p2 : Ast.proposition) (p : Ast.proposition) (proof1 : T.term)
    (proof2 : T.term) (proof_or : Ast.proof) (args : T.term list) =
  let hp1, prf1, _ =
    create_hypothesis_and_implication_proof context proof1 p1 p
  in
  let hp2, prf2, _ =
    create_hypothesis_and_implication_proof context proof2 p2 p
  in
  parse_application context
    (Ast.OrInd (p1, p2, p, hp1, prf1, hp2, prf2, proof_or))
    p args

and create_hypothesis_and_implication_proof (context : context) (proof : T.term)
    (p : Ast.proposition) (q : Ast.proposition) : string * Ast.proof * context =
  match fst (parse_proof context proof) with
  | Ast.ImplIntro (hp1, _, prf) -> (hp1, prf, context)
  | Ast.Assumption h ->
      let hp1, context = fresh_local_hypothesis context in
      (hp1, Ast.Apply (h, [ Ast.TProof (Ast.Assumption hp1) ]), context)
  | Ast.GlobalAssumption h ->
      let hp1, context = fresh_local_hypothesis context in
      (hp1, Ast.ApplyTheorem (h, [ Ast.TProof (Ast.Assumption hp1) ]), context)
  | prf ->
      let hp1, context = fresh_local_hypothesis context in
      let himp, context = fresh_local_hypothesis context in
      ( hp1,
        Ast.Cut
          ( Ast.Implication (p, q),
            prf,
            himp,
            Ast.Apply (himp, [ Ast.TProof (Ast.Assumption hp1) ]) ),
        context )

and parse_and_elim (context : context) (p1 : T.term) (p2 : T.term) (p : T.term)
    (proof_p : T.term) (proof_and : T.term) (args : T.term list) =
  let p1 = parse_proposition context p1 in
  let p2 = parse_proposition context p2 in
  let p = parse_proposition context p in
  let proof_and, _ = parse_proof context proof_and in
  parse_and_elim_ context p1 p2 p proof_p proof_and args

and parse_and_elim_ (context : context) (p1 : Ast.proposition)
    (p2 : Ast.proposition) (p : Ast.proposition) (proof_p : T.term)
    (proof_and : Ast.proof) (args : T.term list) =
  let hp1, hp2, prfp, _ =
    match proof_p with
    | T.Lam (_, hp1, _, proof) ->
        let hp1 = B.string_of_ident hp1 in
        let hp1, context = declare_local_hypothesis hp1 context p1 in
        let hp2, proof, context =
          create_hypothesis_and_implication_proof context proof p2 p
        in
        (hp1, hp2, proof, context)
    | _ ->
        let hp1, context = fresh_local_hypothesis context in
        let hp2, context = fresh_local_hypothesis context in
        let proof =
          match fst (parse_proof context proof_p) with
          | Ast.Assumption h ->
              Ast.Apply
                ( h,
                  [
                    Ast.TProof (Ast.Assumption hp1);
                    Ast.TProof (Ast.Assumption hp2);
                  ] )
          | Ast.GlobalAssumption h ->
              Ast.ApplyTheorem
                ( h,
                  [
                    Ast.TProof (Ast.Assumption hp1);
                    Ast.TProof (Ast.Assumption hp2);
                  ] )
          | prfimp ->
              let cutprop = Ast.Implication (Ast.Implication (p1, p2), p) in
              let hcut, _ = fresh_local_hypothesis context in
              Ast.Cut
                ( cutprop,
                  prfimp,
                  hcut,
                  Ast.Apply
                    ( hcut,
                      [
                        Ast.TProof (Ast.Assumption hp1);
                        Ast.TProof (Ast.Assumption hp2);
                      ] ) )
        in
        (hp1, hp2, proof, context)
  in
  parse_application context
    (Ast.AndInd (hp1, p1, hp2, p2, proof_and, p, prfp))
    p args

and parse_and_elim_l (context : context) (p1 : T.term) (p2 : T.term)
    (p : T.term) (proof_p : T.term) (proof_and : T.term) (args : T.term list) =
  let p1 = parse_proposition context p1 in
  let p2 = parse_proposition context p2 in
  let p = parse_proposition context p in
  let proof_and, _ = parse_proof context proof_and in
  let hp1, prfp, _ =
    create_hypothesis_and_implication_proof context proof_p p1 p
  in
  parse_application context
    (Ast.AndIndLeft (hp1, p1, p2, proof_and, p, prfp))
    p args

and parse_and_elim_r (context : context) (p1 : T.term) (p2 : T.term)
    (p : T.term) (proof_p : T.term) (proof_and : T.term) (args : T.term list) =
  let p1 = parse_proposition context p1 in
  let p2 = parse_proposition context p2 in
  let p = parse_proposition context p in
  let proof_and, _ = parse_proof context proof_and in
  let hp2, prfp, _ =
    create_hypothesis_and_implication_proof context proof_p p2 p
  in
  parse_application context
    (Ast.AndIndRight (p1, hp2, p2, proof_and, p, prfp))
    p args

and parse_ex_elim_ (context : context) (abs : Ast.abstraction)
    (q : Ast.proposition) (proof_imp : T.term) (proof_ex : Ast.proof)
    (args : T.term list) : Ast.rule * Ast.proposition =
  let set, x, prop = abs in
  let wit_name, h, proof_imp, _ =
    match proof_imp with
    | T.Lam (_, wit, _, proof) ->
        let wit = B.string_of_ident wit in
        let wit_name, context = declare_local_element wit context set in
        let p = Ast.instantiate x prop (Ast.ElementCst wit_name) in
        let hp, proof, context =
          create_hypothesis_and_implication_proof context proof p q
        in
        (wit_name, hp, proof, context)
    | _ ->
        let wit_name, context = fresh_local_element set context in
        let wit = Ast.Variable wit_name in
        let hp, context = fresh_local_hypothesis context in
        let proof =
          match fst (parse_proof context proof_imp) with
          | Ast.Assumption h ->
              Ast.Apply (h, [ Ast.TElement wit; Ast.TProof (Ast.Assumption hp) ])
          | Ast.GlobalAssumption h ->
              Ast.ApplyTheorem
                (h, [ Ast.TElement wit; Ast.TProof (Ast.Assumption hp) ])
          | prfimp ->
              let cutprop = Ast.Implication (Ast.Forall abs, q) in
              let hcut, _ = fresh_local_hypothesis context in
              Ast.Cut
                ( cutprop,
                  prfimp,
                  hcut,
                  Ast.Apply
                    (hcut, [ Ast.TElement wit; Ast.TProof (Ast.Assumption hp) ])
                )
        in
        (wit_name, hp, proof, context)
  in
  parse_application context
    (Ast.ExInd (abs, q, proof_ex, wit_name, h, proof_imp))
    q args

and parse_ex_elim (context : context) (setn : B.name) (x : B.ident)
    (prop : T.term) (p : T.term) (proof_p : T.term) (proof_ex : T.term)
    (rest : T.term list) : Ast.proof * Ast.proposition =
  let _ = (context, setn, x, prop, p, proof_p, proof_ex, rest) in
  let set = pair_string_of_name setn in
  let x = B.string_of_ident x in
  let x, context_pred = declare_local_element x context set in
  let prop = parse_proposition context_pred prop in
  let p = parse_proposition context p in
  let proof_ex, _ = parse_proof context proof_ex in
  parse_ex_elim_ context (set, x, prop) p proof_p proof_ex rest

let parse_basic_declaration context name decl =
  match decl with
  | T.Const (_, cst) when is_set cst -> Ast.Set
  | T.App (T.Const (_, cst), T.Const (_, set), []) when is_el cst ->
      let set = pair_string_of_name set in
      Ast.Element set
  | T.App (T.Const (_, cst), args, []) when is_predicate cst ->
      let args = parse_set_list context name args in
      Ast.PredicateSymbol args
  | T.App (T.Const (_, cst), args, [ T.Const (_, return) ]) when is_function cst
    ->
      let args = parse_set_list context name args in
      let ret_type = pair_string_of_name return in
      Ast.FunctionSymbol (args, ret_type)
  | T.App (T.Const (_, cst), statement, []) when is_prf cst ->
      let statement = parse_proposition context statement in
      Ast.Axiom statement
  | _ ->
      raise
        (ParsingError
           "We can only declare sets, elements, predicates, functions and \
            poofs (axioms).")

let parse_basic_definition ty te ctx =
  match ty with
  | T.App (T.Const (_, cst), T.Const (_, set), []) when is_el cst ->
      let set = pair_string_of_name set in
      let el, _ = parse_element ctx te in
      let _ = el in
      Ast.Element set
  | T.App (T.Const (_, cst), _, []) when is_predicate cst ->
      let args, te = parse_predicate_definition ctx te in
      Ast.Predicate (args, te)
  | T.App (T.Const (_, cst), _, [ ret ]) when is_function cst ->
      let args, (te, _) = parse_function_definition ctx te in
      let ret_type =
        match ret with
        | T.Const (_, cst) -> pair_string_of_name cst
        | _ -> failwith "Return type of a function should be a set."
      in
      Ast.Function (args, ret_type, te)
  | T.App (T.Const (_, cst), proposition, []) when is_prf cst ->
      let _ = proposition in
      let proof, prop = parse_proof ctx te in
      Ast.Theorem (prop, proof)
  | _ -> failwith "Error, we can only define functions, predicate and theorems."

let parse_entry (mname : string) globals e =
  let ctx : context = (new_parsing_context, globals) in
  match e with
  | E.Decl (_, id, _, _, decl) ->
      let name = B.string_of_ident id in
      let e = parse_basic_declaration ctx name decl in
      ((mname, name), e)
  | E.Def (_, id, _, _, Some ty, te) ->
      let name = B.string_of_ident id in
      let e = parse_basic_definition ty te ctx in
      ((mname, name), e)
  | _ ->
      raise
        (ParsingError
           "Error, can only translate definitions and declarations, rewrite \
            rules and commands are not accepted.")

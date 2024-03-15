type name = string * string
type variable = string
type set = name

type element =
  | ElementCst of variable
  | Variable of variable
  | GlobalElementCst of name
  | FunctionCall of name * element list

type proposition =
  | True
  | False
  | GlobalProposition of name
  | Forall of abstraction
  | Exists of abstraction
  | Implication of proposition * proposition
  | Conjonction of proposition * proposition
  | Disjonction of proposition * proposition
  | Negation of proposition
  | Equality of set * element * element
  | NotEquality of set * element * element
  | PredicateCall of name * element list
  | ForallList of (set * variable) list * proposition
  | ExistsList of (set * variable) list * proposition

and abstraction = set * variable * proposition (*x: set, (P x) = (set, x, P)*)

let rec collapse_quantifier_in_proposition prop =
  match prop with
  | True -> True
  | False -> False
  | GlobalProposition p -> GlobalProposition p
  | Forall (typ, x, prop) -> (
      match collapse_quantifier_in_proposition prop with
      | ForallList (var_list, prop) -> ForallList ((typ, x) :: var_list, prop)
      | prop -> ForallList ([ (typ, x) ], prop))
  | Exists (typ, x, prop) -> (
      match collapse_quantifier_in_proposition prop with
      | ExistsList (var_list, prop) -> ExistsList ((typ, x) :: var_list, prop)
      | prop -> ExistsList ([ (typ, x) ], prop))
  | Implication (p, q) ->
      Implication
        ( collapse_quantifier_in_proposition p,
          collapse_quantifier_in_proposition q )
  | Conjonction (p, q) ->
      Conjonction
        ( collapse_quantifier_in_proposition p,
          collapse_quantifier_in_proposition q )
  | Disjonction (p, q) ->
      Disjonction
        ( collapse_quantifier_in_proposition p,
          collapse_quantifier_in_proposition q )
  | Negation p -> Negation (collapse_quantifier_in_proposition p)
  | Equality (typ, x, y) -> Equality (typ, x, y)
  | NotEquality (typ, x, y) -> NotEquality (typ, x, y)
  | PredicateCall (f, l) -> PredicateCall (f, l)
  | ForallList (args, prop) -> (
      match collapse_quantifier_in_proposition prop with
      | ForallList (var_list, prop) -> ForallList (args @ var_list, prop)
      | prop -> ForallList (args, prop))
  | ExistsList (args, prop) -> (
      match collapse_quantifier_in_proposition prop with
      | ExistsList (var_list, prop) -> ExistsList (args @ var_list, prop)
      | prop -> ExistsList (args, prop))

type assertion = GlobalAssertion of name | LocalAssertion of variable

type proof =
  (* Some rules keep the hypothesis names avoiding the generation of fresh names. *)
  | T
  | FalseElim of proof
  | Assumption of assertion
  | AndIntro of proposition * proposition * proof * proof
  | OrIntroL of proposition * proposition * proof
  | OrIntroR of proposition * proposition * proof
  | ExIntro of abstraction * element * proof
  | ForallIntro of abstraction * proof
  | ImplIntro of variable * proposition * proof
  | AndInd of
      proposition
      * proposition
      * assertion
      * proposition
      * variable
      * variable
      * proof
  | AndIndRight of
      proposition * proposition * assertion * proposition * variable * proof
  | AndIndLeft of
      proposition * proposition * assertion * proposition * variable * proof
  | AndElimRight of proposition * proposition * assertion
  | AndElimLeft of proposition * proposition * assertion
  | OrInd of
      proposition
      * proposition
      * assertion
      * proposition
      * variable
      * proof
      * variable
      * proof
  | ExInd of abstraction * assertion * proposition * variable * variable * proof
  (* (H, A, Pimp, PA) Show A => B as H, and show A.*)
  | Cut of proposition * proof * variable * proof
  | NNPP of proposition * proof
  | Classic of proposition
  | EqElim of abstraction * element * element * assertion * assertion
  | EqElimR of abstraction * element * element * assertion * assertion
  | EqSym of set * element * element * proof
  | EqRefl of set * element
  | EqTrans of set * element * element * element * proof * proof
  | Apply of assertion * term list
    (* Use another theorem, replace it by ImplElim and ForallElim. *)
  | ForallElim of abstraction * proof * element
  | ImplElim of variable * proposition * proof * proof

and term = TElement of element | TAssertion of assertion

(** Instantiation functions **)

let rec instantiate_in_element (id : variable) (el : element) (t : element) =
  match el with
  | Variable x when id = x -> t
  | FunctionCall (f, l) ->
      FunctionCall (f, List.map (fun el -> instantiate_in_element id el t) l)
  | _ -> el

let rec instantiate_in_prop (id : variable) (t : element) (p : proposition) =
  match p with
  | Implication (p, q) ->
      Implication (instantiate_in_prop id t p, instantiate_in_prop id t q)
  | Conjonction (p, q) ->
      Conjonction (instantiate_in_prop id t p, instantiate_in_prop id t q)
  | Disjonction (p, q) ->
      Disjonction (instantiate_in_prop id t p, instantiate_in_prop id t q)
  | Negation p -> Negation (instantiate_in_prop id t p)
  | Equality (set, x, y) ->
      Equality
        (set, instantiate_in_element id x t, instantiate_in_element id y t)
  | NotEquality (set, x, y) ->
      NotEquality
        (set, instantiate_in_element id x t, instantiate_in_element id y t)
  | PredicateCall (f, l) ->
      PredicateCall (f, List.map (fun el -> instantiate_in_element id el t) l)
  | Forall (set, y, p) when id <> y ->
      Forall (set, y, instantiate_in_prop id t p)
  | Exists (set, y, p) when id <> y ->
      Exists (set, y, instantiate_in_prop id t p)
  | ForallList (args, p) when not (List.mem id (List.map snd args)) ->
      ForallList (args, instantiate_in_prop id t p)
  | ExistsList (args, p) when not (List.mem id (List.map snd args)) ->
      ExistsList (args, instantiate_in_prop id t p)
  | _ -> p

type entry =
  | Set
  | Element of name
  | PredicateSymbol of name list
  | Predicate of (variable * name) list * proposition
  | FunctionSymbol of name list * name
  | Function of (variable * name) list * name * element
  | Axiom of proposition
  | Theorem of proposition * proof

type arguments = (variable * set) list
type local_elements = (variable * name) list
type local_hypothesis = (variable * proposition) list
type _local_context = local_elements * local_hypothesis
type global_elements = (name * (set * element option)) list
type global_hypothesis = (name * proposition) list

type global_predicates =
  (name * (set list * (variable list * proposition) option)) list

type global_functions =
  (name * ((set list * set) * (variable list * element) option)) list

type global_sets = name list

type _global_context =
  global_elements
  * global_hypothesis
  * global_predicates
  * global_functions
  * global_sets

let local_elements (c : _local_context) : local_elements = fst c
let local_hypothesis (c : _local_context) : local_hypothesis = snd c

let declare_local_element (x : variable) (set : name) (c : _local_context) :
    _local_context =
  ((x, set) :: List.remove_assoc x (fst c), snd c)

let declare_local_hypothesis (x : variable) (p : proposition)
    (c : _local_context) : _local_context =
  (fst c, (x, p) :: List.remove_assoc x (snd c))

let empty_global_context : _global_context = ([], [], [], [], [])

let global_predicates (c : _global_context) : global_predicates =
  let _, _, p, _, _ = c in
  p

let global_functions (c : _global_context) : global_functions =
  let _, _, _, f, _ = c in
  f

let global_elements (c : _global_context) : global_elements =
  let e, _, _, _, _ = c in
  e

let global_hypothesis (c : _global_context) : global_hypothesis =
  let _, h, _, _, _ = c in
  h

let global_sets (c : _global_context) : global_sets =
  let _, _, _, _, s = c in
  s

let set_exist (x : name) (c : _global_context) : bool =
  List.mem x (global_sets c)

let declare_global_hypothesis (x : name) (p : proposition) (c : _global_context)
    : _global_context =
  let elements, hypothesis, predicates_, functions, sets = c in
  ( elements,
    (x, p) :: List.remove_assoc x hypothesis,
    predicates_,
    functions,
    sets )

let declare_global_element (x : name) (set : set) (c : _global_context) :
    _global_context =
  let elements, hypothesis, predicates_, functions, sets = c in
  ( (x, (set, None)) :: List.remove_assoc x elements,
    hypothesis,
    predicates_,
    functions,
    sets )

let define_global_element (x : name) (set : set) (e : element)
    (c : _global_context) : _global_context =
  let elements, hypothesis, predicates_, functions, sets = c in
  ( (x, (set, Some e)) :: List.remove_assoc x elements,
    hypothesis,
    predicates_,
    functions,
    sets )

let declare_global_set (x : name) (c : _global_context) : _global_context =
  let elements, hypothesis, predicates_, functions, sets = c in
  (elements, hypothesis, predicates_, functions, x :: sets)

let declare_global_predicate (x : name) (args_types : set list)
    (c : _global_context) : _global_context =
  let elements, hypothesis, predicates, functions, sets = c in
  (elements, hypothesis, (x, (args_types, None)) :: predicates, functions, sets)

let define_global_predicate (x : name) (args_with_type : (variable * set) list)
    (prop : proposition) (c : _global_context) : _global_context =
  let elements, hypothesis, predicates, functions, sets = c in
  let ids = List.map fst args_with_type in
  let args_types = List.map snd args_with_type in
  ( elements,
    hypothesis,
    (x, (args_types, Some (ids, prop))) :: predicates,
    functions,
    sets )

let declare_global_function (x : name) (args_types : set list) (ret : set)
    (c : _global_context) : _global_context =
  let elements, hypothesis, predicates, functions, sets = c in
  ( elements,
    hypothesis,
    predicates,
    (x, ((args_types, ret), None)) :: functions,
    sets )

let define_global_function (x : name) (args_with_type : (variable * set) list)
    (ret : set) (el : element) (c : _global_context) : _global_context =
  let elements, hypothesis, predicates, functions, sets = c in
  let ids = List.map fst args_with_type in
  let args_types = List.map snd args_with_type in
  ( elements,
    hypothesis,
    predicates,
    (x, ((args_types, ret), Some (ids, el))) :: functions,
    sets )

let rec call_predicate (prop : proposition) (params : variable list)
    (args : element list) : proposition =
  match (params, args) with
  | [], [] -> prop
  | id :: params, x :: args ->
      call_predicate (instantiate_in_prop id x prop) params args
  | _ -> failwith "Predicate applied to bad arguments number."

let rec not_free_in_element (id : variable) (t : element) : bool =
  match t with
  | Variable x when id = x -> false
  | ElementCst _ | GlobalElementCst _ | Variable _ | FunctionCall (_, []) ->
      true
  | FunctionCall (f, x :: l) ->
      not_free_in_element id x && not_free_in_element id (FunctionCall (f, l))

let rec not_free_in_proposition (id : variable) (prop : proposition) : bool =
  match prop with
  | True | False | GlobalProposition _ -> true
  | Equality (_, x, y) | NotEquality (_, x, y) ->
      not_free_in_element id x && not_free_in_element id y
  | PredicateCall (f, l) -> not_free_in_element id (FunctionCall (f, l))
  | (Forall (_, h, _) | Exists (_, h, _)) when h = id -> true
  | Forall (_, _, p) | Exists (_, _, p) -> not_free_in_proposition id p
  | Implication (p, q) | Conjonction (p, q) | Disjonction (p, q) ->
      not_free_in_proposition id p && not_free_in_proposition id q
  | Negation p | ForallList (_, p) | ExistsList (_, p) ->
      not_free_in_proposition id p

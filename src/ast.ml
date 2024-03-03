type name = string * string
type variable = string

type element =
  | ElementCst of variable
  | Variable of variable
  | GlobalElementCst of name
  | FunctionCall of name * element list

type proposition =
  | True
  | False
  | GlobalProposition of name
    (* If someone declare an axiom (for instance I: True) and want to prove True using I... *)
  | Forall of abstraction
  | Exists of abstraction
  | Implication of proposition * proposition
  | Conjonction of proposition * proposition
  | Disjonction of proposition * proposition
  | Negation of proposition
  | Equality of name * element * element
  | NotEquality of name * element * element
  | PredicateCall of name * element list

and abstraction = name * variable * proposition (*x: set, (P x) = (set, x, P)*)

type rule =
  (* Some rules keep the hypothesis names avoiding the generation of fresh names. *)
  | T
  | FalseElim of proof
  | Assumption of variable
  | GlobalAssumption of name (* To distinguish theorem and context hypothesis *)
  | AndIntro of proposition * proposition * proof * proof
  | AndInd of
      variable
      * proposition
      * variable
      * proposition
      * proof
      * proposition
      * proof
  | AndIndRight of
      proposition * variable * proposition * proof * proposition * proof
  | AndIndLeft of
      variable * proposition * proposition * proof * proposition * proof
  | AndElimRight of proposition * proposition * proof
  | AndElimLeft of proposition * proposition * proof
  | OrIntroL of proposition * proposition * proof
  | OrIntroR of proposition * proposition * proof
  | OrInd of
      proposition
      * proposition
      * proposition
      * variable
      * proof
      * variable
      * proof
      * proof
  | ExIntro of abstraction * element * proof
  | ExInd of abstraction * proposition * proof * variable * variable * proof
  | ForallIntro of abstraction * proof
  | ForallElim of abstraction * proof * element
  | ImplIntro of variable * proposition * proof
  | ImplElim of variable * proposition * proof * proof
    (* (H, A, Pimp, PA) Show A => B as H, and show A.*)
  | Cut of proposition * proof * variable * proof
  | NNPP of proposition * proof
  | Classic of proposition
  | EqElim of
      abstraction * element * element * variable * proof * variable * proof
  | EqElimR of
      abstraction * element * element * variable * proof * variable * proof
  | EqSym of name * element * element * proof
  | EqRefl of name * element
  | EqTrans of name * element * element * element * proof * proof
  | Apply of variable * term list
    (* Use another theorem, replace it by ImplElim and ForallElim. *)
  | ApplyTheorem of name * term list

and proof = rule (* proposition * rule *)
and term = TElement of element | TProof of proof
(* | Proposition of proposition *)

type entry =
  | Set
  | Element of name
  | PredicateSymbol of name list
  | Predicate of (variable * name) list * proposition
  | FunctionSymbol of name list * name
  | Function of (variable * name) list * name * element
  | Axiom of proposition
  | Theorem of proposition * proof

type declarations = string * string * entry

type context_element =
  | SetC
  | HypothesisC of proposition
  | ElementC of name
  | FunctionC of name list * name
  | PredicateC of name list

type global_context = (name * context_element) list
type local_context = (variable * context_element) list

(** New context definitions  **)

type set = name
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

(** End New context definitions **)

let rec replace_el (id : variable) (el : element) (t : element) =
  match el with
  | Variable x when id = x -> t
  | FunctionCall (f, l) ->
      FunctionCall (f, List.map (fun el -> replace_el id el t) l)
  | _ -> el

and instantiate (id : variable) (p : proposition) (t : element) =
  match p with
  | Implication (p, q) -> Implication (instantiate id p t, instantiate id q t)
  | Conjonction (p, q) -> Conjonction (instantiate id p t, instantiate id q t)
  | Disjonction (p, q) -> Disjonction (instantiate id p t, instantiate id q t)
  | Negation p -> Negation (instantiate id p t)
  | Equality (set, x, y) -> Equality (set, replace_el id x t, replace_el id y t)
  | NotEquality (set, x, y) ->
      NotEquality (set, replace_el id x t, replace_el id y t)
  | PredicateCall (f, l) ->
      PredicateCall (f, List.map (fun el -> replace_el id el t) l)
  | Forall (set, y, p) when id <> y -> Forall (set, y, instantiate id p t)
  | Exists (set, y, p) when id <> y -> Exists (set, y, instantiate id p t)
  | _ -> p

and instantiate_in_term (id : variable) (x : element) (te : term) : term =
  match te with
  | TElement y -> TElement (replace_el id y x)
  | TProof p -> TProof (instantiate_in_proof id x p)

and instantiate_in_proof (x : variable) (t : element) (p : proof) : proof =
  match p with
  | T -> T
  | FalseElim prf -> FalseElim (instantiate_in_proof x t prf)
  | Assumption y -> Assumption y
  | GlobalAssumption y -> GlobalAssumption y
  | AndIntro (p, q, prfp, prfq) ->
      AndIntro
        (p, q, instantiate_in_proof x t prfp, instantiate_in_proof x t prfq)
  | AndInd (hp, p, hq, q, prfand, r, prf) ->
      let prf =
        if hp = x || hq = x then prf else instantiate_in_proof x t prf
      in
      AndInd (hp, p, hq, q, instantiate_in_proof x t prfand, r, prf)
  | AndIndLeft (hp, p, q, prfand, r, prf) ->
      let prf = if hp = x then prf else instantiate_in_proof x t prf in
      AndIndLeft (hp, p, q, instantiate_in_proof x t prfand, r, prf)
  | AndIndRight (p, hq, q, prfand, r, prf) ->
      let prf = if hq = x then prf else instantiate_in_proof x t prf in
      AndIndRight (p, hq, q, instantiate_in_proof x t prfand, r, prf)
  | AndElimLeft (p, q, prf) -> AndElimLeft (p, q, instantiate_in_proof x t prf)
  | AndElimRight (p, q, prf) -> AndElimRight (p, q, instantiate_in_proof x t prf)
  | OrIntroL (p, q, prf) -> OrIntroL (p, q, instantiate_in_proof x t prf)
  | OrIntroR (p, q, prf) -> OrIntroR (p, q, instantiate_in_proof x t prf)
  | OrInd (p, q, r, h1, p1, h2, p2, prfor) ->
      let p1 = if h1 = x then p1 else instantiate_in_proof x t p1 in
      let p2 = if h2 = x then p2 else instantiate_in_proof x t p2 in
      OrInd (p, q, r, h1, p1, h2, p2, instantiate_in_proof x t prfor)
  | ExIntro (pred, e, prf) -> ExIntro (pred, e, instantiate_in_proof x t prf)
  | ExInd (pred, p, prfex, x, h, prf) ->
      let prf = if h = x then prf else instantiate_in_proof x t prf in
      ExInd (pred, p, instantiate_in_proof x t prfex, x, h, prf)
  | ForallIntro (pred, prf) -> ForallIntro (pred, instantiate_in_proof x t prf)
  | ForallElim (pred, prf, e) ->
      ForallElim (pred, instantiate_in_proof x t prf, e)
  | ImplIntro (h, p, prf) ->
      let prf = if h = x then prf else instantiate_in_proof x t prf in
      ImplIntro (h, p, instantiate_in_proof x t prf)
  | ImplElim (h, p, prfimp, prf) ->
      let prf = if h = x then prf else instantiate_in_proof x t prf in
      ImplElim (h, p, prfimp, instantiate_in_proof x t prf)
  | Cut (p, prfp, h, prf) ->
      let prf = if h = x then prf else instantiate_in_proof x t prf in
      Cut (p, instantiate_in_proof x t prfp, h, prf)
  | NNPP (p, prf) -> NNPP (p, instantiate_in_proof x t prf)
  | EqElim (pred, y, z, hprf, prfeq, heq, prf) ->
      EqElim
        ( pred,
          y,
          z,
          hprf,
          instantiate_in_proof x t prfeq,
          heq,
          instantiate_in_proof x t prf )
  | EqElimR (pred, y, z, hprf, prfeq, heq, prf) ->
      EqElimR
        ( pred,
          y,
          z,
          hprf,
          instantiate_in_proof x t prfeq,
          heq,
          instantiate_in_proof x t prf )
  | EqSym (set, y, z, prf) -> EqSym (set, y, z, instantiate_in_proof x t prf)
  | EqRefl (set, y) -> EqRefl (set, y)
  | EqTrans (set, u, v, w, prf1, prf2) ->
      EqTrans
        ( set,
          u,
          v,
          w,
          instantiate_in_proof x t prf1,
          instantiate_in_proof x t prf2 )
  | Apply (_, _) | ApplyTheorem (_, _) -> failwith "TODO"
  | Classic p -> Classic p

let bounded_variables (p : proposition) : variable list =
  let rec aux (p : proposition) (l : variable list) : variable list =
    match p with
    | Implication (p, q) | Conjonction (p, q) | Disjonction (p, q) ->
        aux p (aux q l)
    | Negation p -> aux p l
    | Exists (_, x, p) | Forall (_, x, p) -> aux p (x :: l)
    | _ -> l
  in
  aux p []

let vars_in_el (t : element) : variable list =
  let rec aux (t : element) (l : variable list) : variable list =
    match t with
    | ElementCst x -> x :: l
    | Variable x -> x :: l
    | GlobalElementCst _ -> l
    | FunctionCall (_, args) -> List.fold_left (fun l t -> aux t l) l args
  in
  aux t []

(*
   let instantiate_alpha (id: variable) (p: proposition) (t: element) =
*)

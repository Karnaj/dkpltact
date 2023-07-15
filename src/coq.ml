type name = string * string
type variable = string 

type coq_element = 
  | ElementCst of variable
  | GlobalElementCst of name
  | FunctionCall of name * coq_element list

type coq_prop = 
  | True
  | False
  | PropositionCst of variable
  | GlobalProposition of name
  | Forall of (name * variable) list * coq_prop
  | Exists of (name * variable) list * coq_prop
  | Implication of coq_prop * coq_prop
  | Conjonction of coq_prop * coq_prop
  | Disjonction of coq_prop * coq_prop
  | Negation of coq_prop
  | Equality of name * coq_element * coq_element
  | PredicateCall of name * coq_element list

(*
type coq_proof = 
  | T
  | Contradiction of proof
  | Assumption of variable
  | GlobalAssumption of variable
  | AndIntro of coq_prop * coq_prop * proof * proof
  | AndInd of variable * proposition * variable * proposition * proof * proposition * proof
  | OrIntroL of proposition * proposition * proof
  | OrIntroR of proposition * proposition * proof
  | OrInd of proposition * proposition * proposition * variable * proof * variable * proof * proof 
  | ExIntro of predicate * element * proof 
  | ExInd of predicate * proposition * proof * variable * variable * proof
  | ForallIntro of predicate * proof
  | ForallElim of predicate * proof * element
  | ImplIntro of variable * proposition * proof 
  | ImplElim of variable * proposition * proof * proof (* (H, A, Pimp, PA) Show A => B as H, and show A.*)
  | Apply of name * term list (* Use another theorem, replace it by ImplElim and ForallElim. *)
  | Cut of proposition * proof * variable * proof
  | NNPP of proposition * proof
  | EqElim of predicate * element * element * proof * proof
  | EqElimR of predicate * element * element * proof * proof
  | EqSym of predicate * element * element * proof * proof
  | EqRefl of predicate * element * element * proof * proof 
  | EqTrans of predicate * element * element * element * proof * proof * proof   
*)


(*translate_proof p = match p with
  | Ast.T -> Ast.T
  | Ast.FalseElim(p) -> Contradiction(translate_proof p)
  | Ast.Assumption(x) -> Assumption(x)
  | Ast.GlobalAssumption(x) -> GlobalAssumption(x)
  | Ast.AndIntro(p, q, prf_p, prf_q) ->
      let p = translate_proposition p in
      let q = translate_proposition q in 
      let prf_p = translate_proof prf_p in 
      let prf_q = translate_proof prf_q in 
  | Ast.AndInd(p, q, prf_p, prf_q) ->
      let p = translate_proposition p in
      let q = translate_proposition q in 
      let prf_and = translate_proof prf_and in 
      let prf = translate_proof prf in 
      AndInd(p, q, prf_and, hp, pq, r, prf)
  | 


and*) 
let rec translate_proof p = p 

and translate_element x = match x with
  | Ast.ElementCst(x) -> ElementCst(x)
  | Ast.GlobalElementCst(x) -> GlobalElementCst(x)
  | Ast.FunctionCall(f, l) -> FunctionCall(f, List.map translate_element l)

and translate_proposition prop = match prop with 
  | Ast.True -> True
  | Ast.False -> False
  | Ast.PropositionCst(p) -> PropositionCst(p)
  | Ast.GlobalProposition(p) -> GlobalProposition(p)
  | Ast.Forall(typ, x, prop) -> 
    begin match translate_proposition prop with
      | Forall(var_list, prop) -> Forall((typ, x)::var_list, prop)
      | prop -> Forall([(typ, x)], prop)
    end
  | Ast.Exists((typ, x, prop)) -> 
      begin match translate_proposition prop with
        | Exists(var_list, prop) -> Exists((typ, x)::var_list, prop)
        | prop -> Exists([(typ, x)], prop)
      end
  | Ast.Implication(p, q) -> Implication(translate_proposition p, translate_proposition q)
  | Ast.Conjonction(p, q) -> Conjonction(translate_proposition p, translate_proposition q)
  | Ast.Disjonction(p, q) -> Disjonction(translate_proposition p, translate_proposition q)
  | Ast.Negation(p) -> Negation(translate_proposition p)
  | Ast.Equality(typ, x, y) -> Equality(typ, translate_element x, translate_element y)
  | PredicateCall(f, l) -> PredicateCall(f, List.map translate_element l)



let string_of_name f = if fst f = "" then snd f else (fst f) ^ "." ^ (snd f)

let string_with_or_without_par str cond = if cond then Printf.sprintf "(%s)" str else Printf.sprintf "%s" str


let is_atomic_element el = match el with
  | ElementCst(_) -> true 
  | GlobalElementCst(_) -> true
  | _ -> false 

let string_of_args args verbose = 
  let _ = verbose in
  let format_arg = (fun arg -> Printf.sprintf "(%s: %s) " (fst arg) (string_of_name (snd arg))) in 
  let args_string = List.map format_arg args in
  List.fold_left (fun str arg -> str ^ arg) " " args_string 

let rec string_of_paramaters_type (args: name list) = match args with
  | [] -> ""
  | [x] -> string_of_name x
  | x::args -> (string_of_name x) ^ " -> " ^ (string_of_paramaters_type args)
  
let rec string_of_call f args = 
  let format_arg = (fun arg -> string_with_or_without_par (string_of_coq_element arg) (not (is_atomic_element arg))) in
  let args_string = List.map format_arg args in
  let arg_string = List.fold_left (fun str arg -> str ^ " " ^ arg) "" args_string in
  Printf.sprintf "%s%s" (string_of_name f) arg_string

and string_of_coq_element x = match x with 
  | ElementCst(x) -> x
  | GlobalElementCst(x) -> string_of_name x
  | FunctionCall(f, args) -> string_of_call f args

let is_atomic_prop p = match p with
  | True | False | PropositionCst(_) -> true
  | _ -> false

let rec string_of_coq_prop prop = match prop with 
  | True -> "True"
  | False -> "False"
  | PropositionCst(p) -> p
  | GlobalProposition(p) -> string_of_name p
  | Forall(l, prop) -> 
    let args = List.fold_left (fun s var -> s ^ " " ^ (snd var)) "" l in
    Printf.sprintf "forall%s, %s" args (string_of_coq_prop prop)
  | Exists(l, prop) -> 
      let args = List.fold_left (fun s var -> s ^ " " ^ (snd var)) "" l in
      Printf.sprintf "exists%s, %s" args (string_of_coq_prop prop)
  | Implication(p, q) -> 
      let pstring = string_of_coq_prop p in
      let qstring = string_of_coq_prop q in
      let pparenthesis = begin match p with
        | Implication(_, _) -> true
        | _ -> false 
      end in if pparenthesis then Printf.sprintf "(%s) -> %s" pstring qstring
      else Printf.sprintf "%s -> %s" pstring qstring
  | Conjonction(p, q) -> 
      let pparenthesis = begin match p with
        | True | False | PropositionCst(_) | Negation(_)| Equality(_, _, _) | PredicateCall(_) -> false
        | _ -> true 
      end in let qparenthesis = begin match q with
        | True | False | PropositionCst(_) | Negation(_)| Equality(_, _, _) | PredicateCall(_) | Conjonction(_, _)-> false
        | _ -> true 
      end in let pstring = string_with_or_without_par (string_of_coq_prop p) pparenthesis in
      let qstring = string_with_or_without_par (string_of_coq_prop q) qparenthesis in
      (*let pstring = if pparenthesis then Printf.sprintf "(%s)" pstring else Printf.sprintf "%s" pstring in
      let qstring = if qparenthesis then Printf.sprintf "(%s)" qstring else Printf.sprintf "%s" qstring in *)
      Printf.sprintf "%s /\\ %s" pstring qstring
  | Disjonction(p, q) -> 
      let pparenthesis = begin match p with
        | True | False | PropositionCst(_) | Negation(_)| Equality(_, _, _) | PredicateCall(_) | Conjonction(_, _) -> false
        | _ -> true 
      end in let qparenthesis = begin match q with
        | True | False | PropositionCst(_) | Negation(_)| Equality(_, _, _) | PredicateCall(_) | Conjonction(_, _) | Disjonction(_, _) -> false
        | _ -> true 
      end in let pstring = string_with_or_without_par (string_of_coq_prop p) pparenthesis in
      let qstring = string_with_or_without_par (string_of_coq_prop q) qparenthesis in
      (*let pstring = if pparenthesis then Printf.sprintf "(%s)" pstring else Printf.sprintf "%s" pstring in
      let qstring = if qparenthesis then Printf.sprintf "(%s)" qstring else Printf.sprintf "%s" qstring in*)
      Printf.sprintf "%s \\/ %s" pstring qstring
  | Negation(p) -> 
    let parenthesis = begin match p with
      | Implication(_, _) | Conjonction(_, _) | Disjonction(_, _) -> true
      | _ -> false
    end in let pstring = string_of_coq_prop p in
    if parenthesis then Printf.sprintf "~(%s)" pstring
    else Printf.sprintf "~%s" pstring
  | Equality(_, p, q) ->
    let pstring = string_of_coq_element p in
    let qstring = string_of_coq_element q in
    Printf.sprintf "%s = %s" pstring qstring
  | PredicateCall(f, args) -> string_of_call f args

let string_of_coq_proof p = match p with
  | Ast.T -> "apply I."
  | _ -> ""


let string_of_decl decl = match decl with
| ((_, s), Ast.Set) -> Printf.sprintf "Definition %s: Set." s
| ((_, x), Ast.Element(set)) -> Printf.sprintf "Definition %s: %s." x (string_of_name set)
| ((_, f), Ast.FunctionSymbol(args, ret)) -> Printf.sprintf "Definition %s: %s -> %s." f (string_of_paramaters_type args) (string_of_name ret) 
| ((_, f), Ast.PredicateSymbol(args)) -> Printf.sprintf "Definition %s: %s -> Prop." f (string_of_paramaters_type args)
| ((_, p), Ast.Axiom(prop)) -> Printf.sprintf "Axiom %s: %s" p (string_of_coq_prop (translate_proposition prop))
| ((_, f), Ast.Predicate(args, prop)) -> Printf.sprintf "Definition %s%s := %s." f (string_of_args args false) (string_of_coq_prop (translate_proposition prop))
| ((_, f), Ast.Function(args, _, te)) -> Printf.sprintf "Definition %s%s:= %s." f (string_of_args args false) (string_of_coq_element (translate_element te))
| ((_, p), Ast.Theorem(prop, proof)) -> Printf.sprintf "Theorem %s: %s\n%s\nQed." p (string_of_coq_prop (translate_proposition prop)) (string_of_coq_proof (translate_proof proof)) 

let x = Conjonction(True, False)
let x = Disjonction(x, True) 
let x = Conjonction(x, False)
let x = Disjonction(False, x)
let x = Conjonction(True, x)

let nat = ("nat", "nat")
let one = GlobalElementCst(("nat", "1"))
let two = GlobalElementCst(("nat", "2"))
let plus = ("nat", "plus")
let add_one = FunctionCall(plus, [one; one])

let eq_string = Equality(nat, two, add_one)

let coq_string_test =
  Disjonction(
    Forall([(("Nat", "nat"), "x"); (("Nat", "nat"), "y"); (("Nat", "nat"), "z")], 
      Conjonction(
        Negation(Implication(Negation(Implication(True, False)), Negation(False))),
        x
      )
    ),
    eq_string
  )
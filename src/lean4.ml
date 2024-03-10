open Ast

let string_of_name (f : Ast.name) : string = snd f

let string_with_or_without_par (str : string) (cond : bool) : string =
  if cond then Printf.sprintf "(%s)" str else Printf.sprintf "%s" str

let is_atomic_element el =
  match el with
  | Ast.Variable _ | Ast.ElementCst _ -> true
  | Ast.GlobalElementCst _ -> true
  | _ -> false

(* Here, modify to (not) have the types of the argument. They can be necesary in some cases,
   and we can try to detect them.
*)
let string_of_args args verbose =
  let _ = verbose in
  let format_arg arg =
    (* Printf.sprintf "%s " (fst arg) *)
    Printf.sprintf "(%s: %s) " (fst arg) (string_of_name (snd arg))
  in
  let args_string = List.map format_arg args in
  List.fold_left (fun str arg -> str ^ arg) " " args_string

let rec string_of_paramaters_type (args : Ast.name list) =
  match args with
  | [] -> ""
  | [ x ] -> string_of_name x
  | x :: args -> string_of_name x ^ " → " ^ string_of_paramaters_type args

let rec string_of_call f args =
  let format_arg arg =
    string_with_or_without_par (string_of_element arg)
      (not (is_atomic_element arg))
  in
  let args_string = List.map format_arg args in
  let arg_string =
    List.fold_left (fun str arg -> str ^ " " ^ arg) "" args_string
  in
  Printf.sprintf "%s%s" (string_of_name f) arg_string

and string_of_element x =
  match x with
  | ElementCst x -> x
  | Variable x -> x
  | GlobalElementCst x -> string_of_name x
  | FunctionCall (f, args) -> string_of_call f args

let is_atomic_prop p =
  match p with True | False | GlobalProposition _ -> true | _ -> false

(* Here, modify to (not) have the types of the argument. They can be necesary in some cases,
   and we can try to detect them.
*)
let rec string_of_prop prop =
  match prop with
  | Ast.True -> "True"
  | Ast.False -> "False"
  | Ast.GlobalProposition p -> string_of_name p
  | Ast.ForallList (l, prop) ->
      let args =
        List.fold_left
          (fun s var ->
            (* Printf.sprintf "%s %s" s (snd var)) *)
            Printf.sprintf "%s (%s: %s)" s (snd var) (string_of_name (fst var)))
          "" l
      in
      Printf.sprintf "∀%s, %s" args (string_of_prop prop)
  | Ast.ExistsList (l, prop) ->
      let args =
        List.fold_left
          (fun s var ->
            (* Printf.sprintf "%s %s" s (snd var)) *)
            Printf.sprintf "%s (%s: %s)" s (snd var) (string_of_name (fst var)))
          "" l
      in
      Printf.sprintf "∃%s, %s" args (string_of_prop prop)
  | Ast.Implication (p, q) ->
      let pstring = string_of_prop p in
      let qstring = string_of_prop q in
      let pparenthesis =
        match p with Ast.Implication (_, _) -> true | _ -> false
      in
      if pparenthesis then Printf.sprintf "(%s) → %s" pstring qstring
      else Printf.sprintf "%s → %s" pstring qstring
  | Ast.Conjonction (p, q) ->
      let pparenthesis =
        match p with
        | Ast.True | Ast.False | Ast.GlobalProposition _ | Ast.Negation _
        | Ast.Equality (_, _, _)
        | Ast.PredicateCall _ ->
            false
        | _ -> true
      in
      let qparenthesis =
        match q with
        | Ast.True | Ast.False | Ast.GlobalProposition _ | Ast.Negation _
        | Ast.Equality (_, _, _)
        | Ast.PredicateCall _
        | Ast.Conjonction (_, _) ->
            false
        | _ -> true
      in
      let pstring =
        string_with_or_without_par (string_of_prop p) pparenthesis
      in
      let qstring =
        string_with_or_without_par (string_of_prop q) qparenthesis
      in
      Printf.sprintf "%s ∧ %s" pstring qstring
  | Ast.Disjonction (p, q) ->
      let pparenthesis =
        match p with
        | Ast.True | Ast.False | Ast.GlobalProposition _ | Ast.Negation _
        | Ast.Equality (_, _, _)
        | Ast.PredicateCall _
        | Ast.Conjonction (_, _) ->
            false
        | _ -> true
      in
      let qparenthesis =
        match q with
        | Ast.True | Ast.False | Ast.GlobalProposition _ | Ast.Negation _
        | Ast.Equality (_, _, _)
        | Ast.PredicateCall _
        | Ast.Conjonction (_, _)
        | Ast.Disjonction (_, _) ->
            false
        | _ -> true
      in
      let pstring =
        string_with_or_without_par (string_of_prop p) pparenthesis
      in
      let qstring =
        string_with_or_without_par (string_of_prop q) qparenthesis
      in
      Printf.sprintf "%s ∨ %s" pstring qstring
  | Negation p ->
      let parenthesis =
        match p with
        | Implication (_, _) | Conjonction (_, _) | Disjonction (_, _) -> true
        | _ -> false
      in
      let pstring = string_of_prop p in
      if parenthesis then Printf.sprintf "¬(%s)" pstring
      else Printf.sprintf "¬%s" pstring
  | Equality (_, p, q) ->
      let pstring = string_of_element p in
      let qstring = string_of_element q in
      Printf.sprintf "%s = %s" pstring qstring
  | NotEquality (_, p, q) ->
      let pstring = string_of_element p in
      let qstring = string_of_element q in
      Printf.sprintf "%s ≠ %s" pstring qstring
  | PredicateCall (f, args) -> string_of_call f args
  | Ast.Forall (set, x, prop) ->
      Printf.sprintf "∀ (%s: %s), %s" x (string_of_name set)
        (string_of_prop prop)
  | Ast.Exists (set, x, prop) ->
      Printf.sprintf "∃ (%s: %s), %s" x (string_of_name set)
        (string_of_prop prop)

type proof_step = Command of string | Step of proof_step list

let rec get_all_intros args p =
  match p with
  | Ast.ForallIntro ((_, x, _), proof) -> get_all_intros (x :: args) proof
  | Ast.ImplIntro (h, _, proof) -> get_all_intros (h :: args) proof
  | _ -> (List.rev args, p)

let string_of_assertion (h : Ast.assertion) : string =
  match h with GlobalAssertion h -> string_of_name h | LocalAssertion h -> h

let string_of_term t =
  match t with
  | Ast.TAssertion h -> string_of_assertion h
  | Ast.TElement t ->
      if is_atomic_element t then string_of_element t
      else Printf.sprintf "(%s)" (string_of_element t)

let string_of_app th args : string =
  Printf.sprintf "%s%s" (string_of_assertion th)
    (List.fold_left
       (fun str arg -> Printf.sprintf "%s %s" str (string_of_term arg))
       "" args)

let apply th args : string = Printf.sprintf "apply (%s)" (string_of_app th args)




let rec no_block_proof p indent = string_of_proof p indent

and not_indented_block_proof p indent =
  let _ = indent in
  let indent = "  " in
  let str = string_of_proof p indent in
  "·" ^ String.sub str 1 (String.length str - 1)

and indented_block_proof p indent =
  let str = string_of_proof p (indent ^ "  ") in
  let size = 1 + String.length indent in
  indent ^ "·" ^ String.sub str size (String.length str - size)

and block_proof p indent = no_block_proof p indent

and string_of_proof p indent =
  match p with
  | Ast.T -> Printf.sprintf "%sexact True.intro" indent
  | Ast.Assumption x ->
      Printf.sprintf "%sexact %s" indent (string_of_assertion x)
  | Ast.FalseElim p ->
      let p = string_of_proof p indent in
      Printf.sprintf "%sexfalso\n%s" indent p
  | Ast.AndIntro (_, _, p1, p2) ->
      let p1 = block_proof p1 indent in
      let p2 = block_proof p2 indent in
      Printf.sprintf "%sconstructor\n%s\n%s" indent p1 p2
  | Ast.AndInd (_, _, h, _, hp, hq, prf) ->
      let prf = string_of_proof prf indent in
      Printf.sprintf "%shave _h := %s\n%sobtain ⟨%s, %s⟩ := _h\n%s" indent
        (string_of_assertion h) indent hp hq prf
  | Ast.AndIndRight (_, _, h, _, hq, prf) ->
      let prf = string_of_proof prf indent in
      Printf.sprintf "%shave _h := %s\n%sobtain ⟨_, %s⟩ := _h\n%s" indent
        (string_of_assertion h) indent hq prf
  | Ast.AndIndLeft (_, _, h, _, hp, prf) ->
      let prf = string_of_proof prf indent in
      Printf.sprintf "%shave _h := %s\n%sobtain ⟨%s, _⟩ := _h\n%s" indent
        (string_of_assertion h) indent hp prf
      (*Printf.sprintf "%scases %s with\n%sintro %s _\n%s" indent
        (string_of_assertion h) indent hp prf *)
  | Ast.AndElimRight (_, _, h) ->
      Printf.sprintf "%sexact And.right %s" indent (string_of_assertion h)
  | Ast.AndElimLeft (_, _, h) ->
      Printf.sprintf "%sexact And.left %s" indent (string_of_assertion h)
  | Ast.OrIntroL (_, _, prf) ->
      let str = string_of_proof prf indent in
      Printf.sprintf "%sleft\n%s" indent str
  | Ast.OrIntroR (_, _, prf) ->
      let str = string_of_proof prf indent in
      Printf.sprintf "%sright\n%s" indent str
  | Ast.OrInd (_, _, h, _, hleft, proofleft, hright, proofright) ->
      let strleft = string_of_proof proofleft ("  " ^ indent) in
      let strright = string_of_proof proofright ("  " ^ indent) in
      Printf.sprintf "%scases %s\n%scase inl %s =>\n%s\n%scase inr %s =>\n%s"
        indent (string_of_assertion h) indent hleft strleft indent hright
        strright
  | Ast.ExIntro (_, x, prf) ->
      let prf = string_of_proof prf indent in
      Printf.sprintf "%suse %s\n%s%ss" indent (string_of_element x) indent prf
  | Ast.ExInd (_, h, _, wit_name, hp, proof_p) ->
      let prf = string_of_proof proof_p indent in
      Printf.sprintf "%shave _h := %s\n%sobtain ⟨%s, %s⟩ := _h\n%s" indent
        (string_of_assertion h) indent wit_name hp prf
  | Ast.ForallIntro ((_, x, _), proof) ->
      let args, proof = get_all_intros [ x ] proof in
      let prf = string_of_proof proof indent in
      Printf.sprintf "%sintro%s\n%s" indent
        (List.fold_left (fun str arg -> Printf.sprintf "%s %s" str arg) "" args)
        prf
  | Ast.ForallElim (_, _, _) ->
      failwith "No more elimination of forall; replaced by application."
  | Ast.ImplIntro (h, _, proof) ->
      let args, proof = get_all_intros [ h ] proof in
      let prf = string_of_proof proof indent in
      Printf.sprintf "%sintro%s\n%s" indent
        (List.fold_left (fun str arg -> Printf.sprintf "%s %s" str arg) "" args)
        prf
  | Ast.ImplElim (_, _, _, _) ->
      failwith "No more elimination of implication; replaced by application."
  | Ast.Cut (_, Ast.Assumption _, _, _) ->
      failwith
        "Assertion where the proof of the assertion is an hypothesis should \
         not happen."
  | Ast.Cut (_, Apply (f, l), h, prf) ->
      let str = string_of_proof prf indent in
      Printf.sprintf "%shave %s := %s\n%s" indent h (string_of_app f l) str
  | Ast.Cut (p, prfp, h, prf) ->
      let str = string_of_proof prf indent in
      let strp = string_of_proof prfp ("  " ^ indent) in
      Printf.sprintf "%shave %s: %s := by\n%s\n%s" indent h
        (string_of_prop (Ast.collapse_quantifier_in_proposition p))
        strp str
  | Ast.Apply (th, args) -> Printf.sprintf "%s%s" indent (apply th args)
  | Ast.NNPP (p, proof) ->
      let proof = string_of_proof proof ("  " ^ indent) in
      Printf.sprintf "%shave _h: %s := by\n%s\n%sapply dne _h" indent
        (string_of_prop
           (Ast.collapse_quantifier_in_proposition
              (Ast.Negation (Ast.Negation p))))
        proof indent
  | Ast.Classic _ -> Printf.sprintf "%sapply em" indent
  | Ast.EqRefl (_, _) -> Printf.sprintf "%srfl" indent
  | Ast.EqSym (_, _, _, proof) ->
      let proof = string_of_proof proof indent in
      Printf.sprintf "%ssymm\n%s" indent proof
  | Ast.EqTrans (_, x, y, _, proof1, proof2) ->
      let proof1 = string_of_proof proof1 ("  " ^ indent) in
      let proof2 = string_of_proof proof2 indent in
      let x = string_of_element x in
      let y = string_of_element y in
      Printf.sprintf "%shave _h: %s = %s := by\n%s\n%srw [_h]\n%s%s" indent x y
        proof1 indent indent proof2
  | Ast.EqElim ((_, id, prop), _, _, hprf, heq) ->
      let prop = string_of_prop (Ast.collapse_quantifier_in_proposition prop) in
      let hprf = string_of_assertion hprf in
      let heq = string_of_assertion heq in
      Printf.sprintf "%sapply Eq.subst (motive := λ%s ↦ %s) %s %s" indent id
        prop heq hprf
  | Ast.EqElimR ((_, id, prop), _, _, hprf, heq) ->
      let prop = string_of_prop (Ast.collapse_quantifier_in_proposition prop) in
      let hprf = string_of_assertion hprf in
      let heq = string_of_assertion heq in
      Printf.sprintf "%sapply  Eq.subst (motive := λ%s ↦ %s) (Eq.symm %s)) %s"
        indent id prop heq hprf

let string_of_decl (decl : (string * string) * Ast.entry) =
  match decl with
  | (_, s), Ast.Set -> Printf.sprintf "inductive %s" s
  | (_, x), Ast.Element set ->
      Printf.sprintf "axiom %s: %s" x (string_of_name set)
  | (_, f), Ast.FunctionSymbol (args, ret) ->
      Printf.sprintf "axiom %s: %s → %s" f
        (string_of_paramaters_type args)
        (string_of_name ret)
  | (_, f), Ast.PredicateSymbol args ->
      Printf.sprintf "axiom %s: %s → Prop" f (string_of_paramaters_type args)
  | (_, p), Ast.Axiom prop ->
      Printf.sprintf "axiom %s: %s" p
        (string_of_prop (Ast.collapse_quantifier_in_proposition prop))
  | (_, f), Ast.Predicate (args, prop) ->
      Printf.sprintf "def %s%s :=\n  %s" f
        (string_of_args args false)
        (string_of_prop (Ast.collapse_quantifier_in_proposition prop))
  | (_, f), Ast.Function (args, _, te) ->
      Printf.sprintf "def %s%s :=\n  %s" f
        (string_of_args args false)
        (string_of_element te)
  | (_, p), Ast.Theorem (prop, proof) ->
      Printf.sprintf "theorem %s: %s := by\n%s" p
        (string_of_prop (Ast.collapse_quantifier_in_proposition prop))
        (string_of_proof proof "  ")

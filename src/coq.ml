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
  | x :: args -> string_of_name x ^ " -> " ^ string_of_paramaters_type args

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
      Printf.sprintf "forall%s, %s" args (string_of_prop prop)
  | Ast.ExistsList (l, prop) ->
      let args =
        List.fold_left
          (fun s var ->
            (* Printf.sprintf "%s %s" s (snd var)) *)
            Printf.sprintf "%s (%s: %s)" s (snd var) (string_of_name (fst var)))
          "" l
      in
      Printf.sprintf "exists%s, %s" args (string_of_prop prop)
  | Ast.Implication (p, q) ->
      let pstring = string_of_prop p in
      let qstring = string_of_prop q in
      let pparenthesis =
        match p with Ast.Implication (_, _) -> true | _ -> false
      in
      if pparenthesis then Printf.sprintf "(%s) -> %s" pstring qstring
      else Printf.sprintf "%s -> %s" pstring qstring
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
      Printf.sprintf "%s /\\ %s" pstring qstring
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
      Printf.sprintf "%s \\/ %s" pstring qstring
  | Negation p ->
      let parenthesis =
        match p with
        | Implication (_, _) | Conjonction (_, _) | Disjonction (_, _) -> true
        | _ -> false
      in
      let pstring = string_of_prop p in
      if parenthesis then Printf.sprintf "~(%s)" pstring
      else Printf.sprintf "~%s" pstring
  | Equality (_, p, q) ->
      let pstring = string_of_element p in
      let qstring = string_of_element q in
      Printf.sprintf "%s = %s" pstring qstring
  | NotEquality (_, p, q) ->
      let pstring = string_of_element p in
      let qstring = string_of_element q in
      Printf.sprintf "%s <> %s" pstring qstring
  | PredicateCall (f, args) -> string_of_call f args
  | Ast.Forall (set, x, prop) ->
      Printf.sprintf "forall (%s: %s), %s" x (string_of_name set)
        (string_of_prop prop)
  | Ast.Exists (set, x, prop) ->
      Printf.sprintf "exists (%s: %s), %s" x (string_of_name set)
        (string_of_prop prop)

type proof_step = Command of string | Step of proof_step list

let symbol_list = [| '-'; '+'; '*' |]

let get_symbol i =
  let bullet = symbol_list.(i mod 3) in
  String.make (1 + (i / 3)) bullet

let rec indent_coq_string_of_string_step_bullet deep i proof =
  match proof with
  | Command str -> Printf.sprintf "%s%s" deep str
  | Step [] -> ""
  | Step (fst :: list) ->
      let symbol = get_symbol i in
      let str =
        Printf.sprintf "%s%s %s" deep symbol
          (indent_coq_string_of_string_step_bullet "" i fst)
      in
      let deep =
        Printf.sprintf "%s%s" deep (String.make (1 + String.length symbol) ' ')
      in
      let f step = indent_coq_string_of_string_step_bullet deep (i + 1) step in
      let str =
        List.fold_left
          (fun str step -> Printf.sprintf "%s\n%s" str (f step))
          str list
      in
      str

let rec coq_string_of_string_step_bullet deep i proof =
  match proof with
  | Command str -> Printf.sprintf "%s%s" deep str
  | Step [] -> ""
  | Step (fst :: list) ->
      let symbol = get_symbol i in
      let str =
        Printf.sprintf "%s %s" symbol
          (coq_string_of_string_step_bullet "" i fst)
      in
      let deep =
        Printf.sprintf "%s" (String.make (1 + String.length symbol) ' ')
      in
      let f step = coq_string_of_string_step_bullet deep (i + 1) step in
      let str =
        List.fold_left
          (fun str step -> Printf.sprintf "%s\n%s" str (f step))
          str list
      in
      str

let rec coq_string_of_string_step_braces deep proof =
  match proof with
  | Command str -> Printf.sprintf "%s%s" deep str
  | Step [] -> ""
  | Step (fst :: list) ->
      let f step =
        coq_string_of_string_step_braces (Printf.sprintf "%s  " deep) step
      in
      let str =
        Printf.sprintf "%s{\n%s  %s" deep deep
          (coq_string_of_string_step_braces "" fst)
      in
      let str =
        List.fold_left
          (fun str step -> Printf.sprintf "%s\n%s" str (f step))
          str list
      in
      Printf.sprintf "%s\n%s}" str deep

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
  Printf.sprintf "@%s%s" (string_of_assertion th)
    (List.fold_left
       (fun str arg -> Printf.sprintf "%s %s" str (string_of_term arg))
       "" args)

let apply th args : string = Printf.sprintf "apply (%s)" (string_of_app th args)

let rec coq_string_step_of_proof p ctx =
  match p with
  | Ast.T -> [ Command "apply I." ]
  | Ast.Assumption x ->
      [ Command (Printf.sprintf "exact %s." (string_of_assertion x)) ]
  | Ast.FalseElim (Ast.Assumption x) ->
      [ Command (Printf.sprintf "contradiction %s." (string_of_assertion x)) ]
  | Ast.FalseElim (Ast.Apply (f, l)) ->
      [ Command (Printf.sprintf "contradiction (%s)." (string_of_app f l)) ]
  | Ast.FalseElim p ->
      let l = coq_string_step_of_proof p ctx in
      Command "exfalso." :: l
  | Ast.AndIntro (_, _, p1, p2) ->
      let l1 = coq_string_step_of_proof p1 ctx in
      let l2 = coq_string_step_of_proof p2 ctx in
      [ Command "split."; Step l1; Step l2 ]
  | Ast.AndInd (_, _, h, _, hp, hq, prf) ->
      let str =
        Printf.sprintf "inversion %s as [%s %s]." (string_of_assertion h) hp hq
      in
      let l = coq_string_step_of_proof prf ctx in
      Command str :: l
  | Ast.AndIndRight (_, _, h, _, hp, prf) ->
      let str =
        Printf.sprintf "inversion %s as [_ %s]." (string_of_assertion h) hp
      in
      let l = coq_string_step_of_proof prf ctx in
      Command str :: l
  | Ast.AndIndLeft (_, _, h, _, hq, prf) ->
      let str =
        Printf.sprintf "inversion %s as [%s _]." (string_of_assertion h) hq
      in
      let l = coq_string_step_of_proof prf ctx in
      Command str :: l
  | Ast.AndElimRight (_, _, h) | Ast.AndElimLeft (_, _, h) ->
      let str = Printf.sprintf "now inversion %s." (string_of_assertion h) in
      [ Command str ]
  | Ast.OrIntroL (_, _, prf) ->
      let str = coq_string_step_of_proof prf ctx in
      Command "left." :: str
  | Ast.OrIntroR (_, _, prf) ->
      let str = coq_string_step_of_proof prf ctx in
      Command "right." :: str
  | Ast.OrInd (_, _, h, _, hleft, proofleft, hright, proofright) ->
      let str1 =
        Printf.sprintf "inversion %s as [%s|%s]." (string_of_assertion h) hleft
          hright
      in
      let strleft = coq_string_step_of_proof proofleft ctx in
      let strright = coq_string_step_of_proof proofright ctx in
      [ Command str1; Step strleft; Step strright ]
  | Ast.ExIntro (_, x, prf) ->
      let str = Printf.sprintf "exists %s." (string_of_element x) in
      let str1 = coq_string_step_of_proof prf ctx in
      Command str :: str1
  | Ast.ExInd (_, h, _, wit_name, hp, proof_p) ->
      let str =
        Printf.sprintf "inversion %s as [%s %s]." (string_of_assertion h)
          wit_name hp
      in
      let str1 = coq_string_step_of_proof proof_p ctx in
      Command str :: str1
  | Ast.ForallIntro ((_, x, _), proof) ->
      let args, proof = get_all_intros [ x ] proof in
      let prf = coq_string_step_of_proof proof ctx in
      let str =
        Printf.sprintf "intros%s."
          (List.fold_left
             (fun str arg -> Printf.sprintf "%s %s" str arg)
             "" args)
      in
      Command str :: prf
  | Ast.ForallElim (_, _, _) ->
      failwith "No more elimination of forall; replaced by application."
  | Ast.ImplIntro (h, _, proof) ->
      let args, proof = get_all_intros [ h ] proof in
      let prf = coq_string_step_of_proof proof ctx in
      let str =
        Printf.sprintf "intros%s."
          (List.fold_left
             (fun str arg -> Printf.sprintf "%s %s" str arg)
             "" args)
      in
      Command str :: prf
  | Ast.ImplElim (_, _, _, _) ->
      failwith "No more elimination of implication; replaced by application."
  | Ast.Cut (_, Ast.Assumption _, _, _) ->
      failwith
        "Assertion where the proof of the assertion is an hypothesis should \
         not happen."
  | Ast.Cut (p, Apply (f, l), h, prf) ->
      let strcut =
        Printf.sprintf "assert (%s) as %s by (%s)."
          (string_of_prop (Ast.collapse_quantifier_in_proposition p))
          h (apply f l)
      in
      let str = coq_string_step_of_proof prf ctx in
      Command strcut :: str
  | Ast.Cut (p, prfp, h, prf) ->
      let strcut =
        Printf.sprintf "assert (%s) as %s."
          (string_of_prop (Ast.collapse_quantifier_in_proposition p))
          h
      in
      let strp = coq_string_step_of_proof prfp ctx in
      let str = coq_string_step_of_proof prf ctx in
      [ Command strcut; Step strp; Step str ]
  | Ast.Apply (th, args) -> [ Command (Printf.sprintf "%s." (apply th args)) ]
  | Ast.NNPP (_, proof) ->
      let proof = coq_string_step_of_proof proof ctx in
      let str = Printf.sprintf "apply NNPP." in
      Command str :: proof
  | Ast.Classic _ ->
      let str = Printf.sprintf "apply classic." in
      [ Command str ]
  | Ast.EqRefl (_, _) -> [ Command "reflexivity." ]
  | Ast.EqSym (_, _, _, proof) ->
      let proof = coq_string_step_of_proof proof ctx in
      let str = Printf.sprintf "symmetry." in
      Command str :: proof
  | Ast.EqTrans (_, _, y, _, proof1, proof2) ->
      let proof1 = coq_string_step_of_proof proof1 ctx in
      let proof2 = coq_string_step_of_proof proof2 ctx in
      let str =
        Printf.sprintf "transitivity %s."
          (string_with_or_without_par (string_of_element y)
             (not (is_atomic_element y)))
      in
      Command str :: Step proof1 :: [ Step proof2 ]
  | Ast.EqElim ((set, id, pred), x, y, hprf, heq)
  | Ast.EqElimR ((set, id, pred), x, y, hprf, heq) ->
      let eqelim =
        match p with
        | Ast.EqElim (_, _, _, _, _) -> "eq_ind"
        | Ast.EqElimR (_, _, _, _, _) -> "eq_ind_r"
        | _ -> failwith "Impossible"
      in
      let eqind =
        Printf.sprintf "apply (@%s %s %s (fun %s => %s) %s %s %s)." eqelim
          (string_of_name set)
          (string_with_or_without_par (string_of_element x)
             (not (is_atomic_element x)))
          id
          (string_of_prop (Ast.collapse_quantifier_in_proposition pred))
          (string_of_assertion hprf)
          (string_with_or_without_par (string_of_element y)
             (not (is_atomic_element y)))
          (string_of_assertion heq)
      in
      [ Command eqind ]

let coq_string_of_proof proof =
  let list = coq_string_step_of_proof proof [] in
  List.fold_left
    (fun str step ->
      Printf.sprintf "%s\n%s" str (coq_string_of_string_step_bullet "  " 0 step))
    "" list

let string_of_decl (decl : (string * string) * Ast.entry) =
  match decl with
  | (_, s), Ast.Set -> Printf.sprintf "Parameter %s: Set." s
  | (_, x), Ast.Element set ->
      Printf.sprintf "Parameter %s: %s." x (string_of_name set)
  | (_, f), Ast.FunctionSymbol (args, ret) ->
      Printf.sprintf "Parameter %s: %s -> %s." f
        (string_of_paramaters_type args)
        (string_of_name ret)
  | (_, f), Ast.PredicateSymbol args ->
      Printf.sprintf "Parameter %s: %s -> Prop." f
        (string_of_paramaters_type args)
  | (_, p), Ast.Axiom prop ->
      Printf.sprintf "Axiom %s: %s." p
        (string_of_prop (Ast.collapse_quantifier_in_proposition prop))
  | (_, f), Ast.Predicate (args, prop) ->
      Printf.sprintf "Definition %s%s := %s." f
        (string_of_args args false)
        (string_of_prop (Ast.collapse_quantifier_in_proposition prop))
  | (_, f), Ast.Function (args, _, te) ->
      Printf.sprintf "Definition %s%s := %s." f
        (string_of_args args false)
        (string_of_element te)
  | (_, p), Ast.Theorem (prop, proof) ->
      Printf.sprintf "Theorem %s: %s.%s\nQed." p
        (string_of_prop (Ast.collapse_quantifier_in_proposition prop))
        (coq_string_of_proof (Proof.simplify_proof proof))

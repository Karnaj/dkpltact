type name = string * string
type variable = string

type coq_element =
  | ElementCst of variable
  | Variable of variable
  | GlobalElementCst of name
  | FunctionCall of name * coq_element list

type coq_prop =
  | True
  | False
  | GlobalProposition of name
  | Forall of (name * variable) list * coq_prop
  | Exists of (name * variable) list * coq_prop
  | Implication of coq_prop * coq_prop
  | Conjonction of coq_prop * coq_prop
  | Disjonction of coq_prop * coq_prop
  | Negation of coq_prop
  | Equality of name * coq_element * coq_element
  | NotEquality of name * coq_element * coq_element
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

and translate_element x =
  match x with
  | Ast.Variable x -> Variable x
  | Ast.ElementCst x -> ElementCst x
  | Ast.GlobalElementCst x -> GlobalElementCst x
  | Ast.FunctionCall (f, l) -> FunctionCall (f, List.map translate_element l)

and translate_proposition prop =
  match prop with
  | Ast.True -> True
  | Ast.False -> False
  | Ast.GlobalProposition p -> GlobalProposition p
  | Ast.Forall (typ, x, prop) -> (
      match translate_proposition prop with
      | Forall (var_list, prop) -> Forall ((typ, x) :: var_list, prop)
      | prop -> Forall ([ (typ, x) ], prop))
  | Ast.Exists (typ, x, prop) -> (
      match translate_proposition prop with
      | Exists (var_list, prop) -> Exists ((typ, x) :: var_list, prop)
      | prop -> Exists ([ (typ, x) ], prop))
  | Ast.Implication (p, q) ->
      Implication (translate_proposition p, translate_proposition q)
  | Ast.Conjonction (p, q) ->
      Conjonction (translate_proposition p, translate_proposition q)
  | Ast.Disjonction (p, q) ->
      Disjonction (translate_proposition p, translate_proposition q)
  | Ast.Negation p -> Negation (translate_proposition p)
  | Ast.Equality (typ, x, y) ->
      Equality (typ, translate_element x, translate_element y)
  | Ast.NotEquality (typ, x, y) ->
      NotEquality (typ, translate_element x, translate_element y)
  | PredicateCall (f, l) -> PredicateCall (f, List.map translate_element l)

let string_of_name f =
  snd f (* if fst f = "" then snd f else (fst f) ^ "." ^ (snd f) *)

let string_with_or_without_par str cond =
  if cond then Printf.sprintf "(%s)" str else Printf.sprintf "%s" str

let is_atomic_element el =
  match el with
  | Variable _ | ElementCst _ -> true
  | GlobalElementCst _ -> true
  | _ -> false

(* Here, modify to (not) have the types of the argument. They can be necesary in some cases, 
   and we can try to detect them.    
*)
let string_of_args args verbose =
  let _ = verbose in
  let format_arg arg =
    Printf.sprintf "%s " (fst arg)
    (* Printf.sprintf "(%s: %s) " (fst arg) (string_of_name (snd arg)) *)
  in
  let args_string = List.map format_arg args in
  List.fold_left (fun str arg -> str ^ arg) " " args_string


let rec string_of_paramaters_type (args : name list) =
  match args with
  | [] -> ""
  | [ x ] -> string_of_name x
  | x :: args -> string_of_name x ^ " -> " ^ string_of_paramaters_type args

let rec string_of_call f args =
  let format_arg arg =
    string_with_or_without_par
      (string_of_coq_element arg)
      (not (is_atomic_element arg))
  in
  let args_string = List.map format_arg args in
  let arg_string =
    List.fold_left (fun str arg -> str ^ " " ^ arg) "" args_string
  in
  Printf.sprintf "%s%s" (string_of_name f) arg_string

and string_of_coq_element x =
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
let rec string_of_coq_prop prop =
  match prop with
  | True -> "True"
  | False -> "False"
  | GlobalProposition p -> string_of_name p
  | Forall (l, prop) ->
      let args =
        List.fold_left
          (fun s var ->
            Printf.sprintf "%s %s" s (snd var))
            (*Printf.sprintf "%s (%s: %s)" s (snd var) (string_of_name (fst var))) *)
          "" l
      in
      Printf.sprintf "forall%s, %s" args (string_of_coq_prop prop)
  | Exists (l, prop) ->
      let args =
        List.fold_left
          (fun s var ->
            Printf.sprintf "%s %s" s (snd var))
            (* Printf.sprintf "%s (%s: %s)" s (snd var) (string_of_name (fst var))) *)
          "" l
      in
      Printf.sprintf "exists%s, %s" args (string_of_coq_prop prop)
  | Implication (p, q) ->
      let pstring = string_of_coq_prop p in
      let qstring = string_of_coq_prop q in
      let pparenthesis =
        match p with Implication (_, _) -> true | _ -> false
      in
      if pparenthesis then Printf.sprintf "(%s) -> %s" pstring qstring
      else Printf.sprintf "%s -> %s" pstring qstring
  | Conjonction (p, q) ->
      let pparenthesis =
        match p with
        | True | False | GlobalProposition _ | Negation _
        | Equality (_, _, _)
        | PredicateCall _ ->
            false
        | _ -> true
      in
      let qparenthesis =
        match q with
        | True | False | GlobalProposition _ | Negation _
        | Equality (_, _, _)
        | PredicateCall _
        | Conjonction (_, _) ->
            false
        | _ -> true
      in
      let pstring =
        string_with_or_without_par (string_of_coq_prop p) pparenthesis
      in
      let qstring =
        string_with_or_without_par (string_of_coq_prop q) qparenthesis
      in
      (*let pstring = if pparenthesis then Printf.sprintf "(%s)" pstring else Printf.sprintf "%s" pstring in
        let qstring = if qparenthesis then Printf.sprintf "(%s)" qstring else Printf.sprintf "%s" qstring in *)
      Printf.sprintf "%s /\\ %s" pstring qstring
  | Disjonction (p, q) ->
      let pparenthesis =
        match p with
        | True | False | GlobalProposition _ | Negation _
        | Equality (_, _, _)
        | PredicateCall _
        | Conjonction (_, _) ->
            false
        | _ -> true
      in
      let qparenthesis =
        match q with
        | True | False | GlobalProposition _ | Negation _
        | Equality (_, _, _)
        | PredicateCall _
        | Conjonction (_, _)
        | Disjonction (_, _) ->
            false
        | _ -> true
      in
      let pstring =
        string_with_or_without_par (string_of_coq_prop p) pparenthesis
      in
      let qstring =
        string_with_or_without_par (string_of_coq_prop q) qparenthesis
      in
      (*let pstring = if pparenthesis then Printf.sprintf "(%s)" pstring else Printf.sprintf "%s" pstring in
        let qstring = if qparenthesis then Printf.sprintf "(%s)" qstring else Printf.sprintf "%s" qstring in*)
      Printf.sprintf "%s \\/ %s" pstring qstring
  | Negation p ->
      let parenthesis =
        match p with
        | Implication (_, _) | Conjonction (_, _) | Disjonction (_, _) -> true
        | _ -> false
      in
      let pstring = string_of_coq_prop p in
      if parenthesis then Printf.sprintf "~(%s)" pstring
      else Printf.sprintf "~%s" pstring
  | Equality (_, p, q) ->
      let pstring = string_of_coq_element p in
      let qstring = string_of_coq_element q in
      Printf.sprintf "%s = %s" pstring qstring
  | NotEquality (_, p, q) ->
      let pstring = string_of_coq_element p in
      let qstring = string_of_coq_element q in
      Printf.sprintf "%s <> %s" pstring qstring
  | PredicateCall (f, args) -> string_of_call f args

(*
let string_of_coq_proof p = match p with
  | Ast.T -> "apply I."
  | _ -> ""
*)

let x = Conjonction (True, False)
let x = Disjonction (x, True)
let x = Conjonction (x, False)
let x = Disjonction (False, x)
let x = Conjonction (True, x)
let nat = ("nat", "nat")
let one = GlobalElementCst ("nat", "1")
let two = GlobalElementCst ("nat", "2")
let plus = ("nat", "plus")
let add_one = FunctionCall (plus, [ one; one ])
let eq_string = Equality (nat, two, add_one)

let coq_string_test =
  Disjonction
    ( Forall
        ( [ (("Nat", "nat"), "x"); (("Nat", "nat"), "y"); (("Nat", "nat"), "z") ],
          Conjonction
            ( Negation
                (Implication
                   (Negation (Implication (True, False)), Negation False)),
              x ) ),
      eq_string )

type proof_step = Command of string | Step of proof_step list

let coq_string_of_prop p = string_of_coq_prop (translate_proposition p)
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

let rec string_of_term t =
  match t with
  | Ast.TProof (GlobalAssumption h) -> string_of_name h
  | Ast.TProof (Assumption h) -> h
  | Ast.TElement t ->
      let t = translate_element t in
      if is_atomic_element t then string_of_coq_element t
      else Printf.sprintf "(%s)" (string_of_coq_element t)
  | _ -> failwith "Nope"

(**
| ImplIntro of variable * proposition * proof 
| ImplElim of variable * proposition * proof * proof (* (H, A, Pimp, PA) Show A => B as H, and show A.*)
| Apply of name * term list (* Use another theorem, replace it by ImplElim and ForallElim. *)
| Cut of proposition * proof * variable * proof
| NNPP of proposition * proof
| EqElim of predicate * element * element * proof * proof
| EqElimR of predicate * element * element * proof * proof
| EqSym of name * element * element * proof
| EqRefl of name * element 
| EqTrans of name * element * element * element * proof * proof 
*)

and is_simply_cut (proof : Ast.proof) : bool =
  match proof with
  | Ast.Assumption _ | Ast.GlobalAssumption _
  | Ast.Apply (_, _)
  | Ast.ApplyTheorem (_, _) ->
      true
  | _ -> false

and simple_cut (proof : Ast.proof) : string =
  match proof with
  | Ast.Assumption h -> Printf.sprintf "exact %s" h
  | Ast.GlobalAssumption h -> Printf.sprintf "exact %s" (string_of_name h)
  | Ast.Apply (th, args) -> Printf.sprintf "apply (%s)" (apply th args)
  | Ast.ApplyTheorem (th, args) ->
      Printf.sprintf "apply (%s)" (apply (string_of_name th) args)
  | _ -> failwith "Impossible."

and apply th args : string = Printf.sprintf "apply (%s)" (string_of_app th args)

and string_of_app th args : string =
  Printf.sprintf "@%s%s" th
    (List.fold_left
       (fun str arg -> Printf.sprintf "%s %s" str (string_of_term arg))
       "" args)

and coq_string_step_of_proof p ctx =
  match p with
  | Ast.T -> [ Command "apply I." ]
  | Ast.Assumption x -> [ Command (Printf.sprintf "exact %s." x) ]
  | Ast.GlobalAssumption x ->
      [ Command (Printf.sprintf "exact %s." (string_of_name x)) ]
  | Ast.FalseElim (Ast.Assumption x) ->
      [ Command (Printf.sprintf "contradiction %s." x) ]
  | Ast.FalseElim (Ast.GlobalAssumption x) ->
      [ Command (Printf.sprintf "contradiction %s." (string_of_name x)) ]
  | Ast.FalseElim (Ast.Apply (f, l)) ->
      [ Command (Printf.sprintf "contradiction (%s)." (string_of_app f l)) ]
  | Ast.FalseElim (Ast.ApplyTheorem (f, l)) ->
      [
        Command
          (Printf.sprintf "contradiction (%s)."
             (string_of_app (string_of_name f) l));
      ]
  | Ast.FalseElim p ->
      let l = coq_string_step_of_proof p ctx in
      Command "exfalso." :: l
  | Ast.AndIntro (_, _, p1, p2) ->
      let l1 = coq_string_step_of_proof p1 ctx in
      let l2 = coq_string_step_of_proof p2 ctx in
      [ Command "split."; Step l1; Step l2 ]
  | Ast.AndInd (hp, _, hq, _, Assumption h, _, prf) ->
      let str = Printf.sprintf "inversion %s as [%s %s]." h hp hq in
      let l = coq_string_step_of_proof prf ctx in
      Command str :: l
  | AndIndRight (_, hq, _, Assumption h, _, prf) ->
      let str = Printf.sprintf "inversion %s as [_ %s]." h hq in
      let l = coq_string_step_of_proof prf ctx in
      Command str :: l
  | AndIndLeft (hp, _, _, Assumption h, _, prf) ->
      let str = Printf.sprintf "inversion %s as [%s _]." h hp in
      let l = coq_string_step_of_proof prf ctx in
      Command str :: l
  | Ast.AndInd (hp, _, hq, _, GlobalAssumption h, _, prf) ->
      let str =
        Printf.sprintf "destruct %s as [%s %s]." (string_of_name h) hp hq
      in
      let l = coq_string_step_of_proof prf ctx in
      Command str :: l
  | Ast.AndIndRight (_, hq, _, GlobalAssumption h, _, prf) ->
      let str = Printf.sprintf "destruct %s as [_ %s]." (string_of_name h) hq in
      let l = coq_string_step_of_proof prf ctx in
      Command str :: l
  | Ast.AndIndLeft (hp, _, _, GlobalAssumption h, _, prf) ->
      let str = Printf.sprintf "destruct %s as [%s _]." (string_of_name h) hp in
      let strprf = coq_string_step_of_proof prf ctx in
      Command str :: strprf
  | Ast.AndInd (hp, p, hq, q, Apply (f, l), _, prf) ->
      let str1 =
        Printf.sprintf "assert (%s) as %s by (%s)."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
          hp (apply f l)
      in
      let str2 = Printf.sprintf "inversion %s as [%s %s]." hp hp hq in
      let strprf = coq_string_step_of_proof prf ctx in
      Command str1 :: Command str2 :: strprf
  | Ast.AndIndRight (p, hq, q, Apply (f, l), _, prf) ->
      let str1 =
        Printf.sprintf "assert (%s) as %s."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
          hq
      in
      let str2 =
        Printf.sprintf "inversion %s as [_ %s] by (%s)." hq hq (apply f l)
      in
      let strprf = coq_string_step_of_proof prf ctx in
      Command str1 :: Command str2 :: strprf
  | Ast.AndIndLeft (hp, p, q, Apply (f, l), _, prf) ->
      let str1 =
        Printf.sprintf "assert (%s) as %s."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
          hp
      in
      let str2 =
        Printf.sprintf "inversion %s as [_ %s] by (%s)." hp hp (apply f l)
      in
      let strprf = coq_string_step_of_proof prf ctx in
      Command str1 :: Command str2 :: strprf
  | Ast.AndInd (hp, p, hq, q, ApplyTheorem (f, l), _, prf) ->
      let str1 =
        Printf.sprintf "assert (%s) as %s by (%s)."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
          hp
          (apply (string_of_name f) l)
      in
      let str2 = Printf.sprintf "inversion %s as [%s %s]." hp hp hq in
      let strprf = coq_string_step_of_proof prf ctx in
      Command str1 :: Command str2 :: strprf
  | Ast.AndIndRight (p, hq, q, ApplyTheorem (f, l), _, prf) ->
      let str1 =
        Printf.sprintf "assert (%s) as %s."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
          hq
      in
      let str2 =
        Printf.sprintf "inversion %s as [_ %s] by (%s)." hq hq
          (apply (string_of_name f) l)
      in
      let strprf = coq_string_step_of_proof prf ctx in
      Command str1 :: Command str2 :: strprf
  | Ast.AndIndLeft (hp, p, q, ApplyTheorem (f, l), _, prf) ->
      let str1 =
        Printf.sprintf "assert (%s) as %s."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
          hp
      in
      let str2 =
        Printf.sprintf "inversion %s as [_ %s] by (%s)." hp hp
          (apply (string_of_name f) l)
      in
      let strprf = coq_string_step_of_proof prf ctx in
      Command str1 :: Command str2 :: strprf
  | Ast.AndInd (hp, p, hq, q, prfand, _, prf) ->
      let str1 =
        Printf.sprintf "assert (%s) as %s."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
          hp
      in
      let str2 = Printf.sprintf "inversion %s as [%s %s]." hp hp hq in
      let strand = coq_string_step_of_proof prfand ctx in
      let strprf = coq_string_step_of_proof prf ctx in
      [ Command str1; Step strand; Step (Command str2 :: strprf) ]
  | Ast.AndIndRight (p, hq, q, prfand, _, prf) ->
      let str1 =
        Printf.sprintf "assert (%s) as %s."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
          hq
      in
      let str2 = Printf.sprintf "inversion %s as [_ %s]." hq hq in
      let strand = coq_string_step_of_proof prfand ctx in
      let strprf = coq_string_step_of_proof prf ctx in
      [ Command str1; Step strand; Step (Command str2 :: strprf) ]
  | Ast.AndIndLeft (hp, p, q, prfand, _, prf) ->
      let str1 =
        Printf.sprintf "assert (%s) as %s."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
          hp
      in
      let str2 = Printf.sprintf "inversion %s as [%s _]." hp hp in
      let strand = coq_string_step_of_proof prfand ctx in
      let strprf = coq_string_step_of_proof prf ctx in
      [ Command str1; Step strand; Step (Command str2 :: strprf) ]
  | Ast.AndElimRight (_, _, Assumption h) ->
      let str = Printf.sprintf "now inversion %s." h in
      [ Command str ]
  | Ast.AndElimLeft (_, _, Assumption h) ->
      let str = Printf.sprintf "now inversion %s." h in
      [ Command str ]
  | Ast.AndElimRight (_, _, GlobalAssumption h) ->
      let str = Printf.sprintf "now destruct %s." (string_of_name h) in
      [ Command str ]
  | Ast.AndElimLeft (_, _, GlobalAssumption h) ->
      let str = Printf.sprintf "now destruct %s." (string_of_name h) in
      [ Command str ]
  | Ast.AndElimRight (p, q, Apply (f, l)) ->
      let str1 =
        Printf.sprintf "assert (%s) as Hand by (%s)."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
          (apply f l)
      in
      let str2 = Printf.sprintf "now inversion Hand." in
      Command str1 :: [ Command str2 ]
  | Ast.AndElimLeft (p, q, Apply (f, l)) ->
      let str1 =
        Printf.sprintf "assert (%s) as Hand by (%s)."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
          (apply f l)
      in
      let str2 = Printf.sprintf "now inversion Hand." in
      Command str1 :: [ Command str2 ]
  | Ast.AndElimRight (p, q, ApplyTheorem (f, l)) ->
      let str1 =
        Printf.sprintf "assert (%s) as Hand by (%s)."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
          (apply (string_of_name f) l)
      in
      let str2 = Printf.sprintf "now inversion Hand." in
      Command str1 :: [ Command str2 ]
  | Ast.AndElimLeft (p, q, ApplyTheorem (f, l)) ->
      let str1 =
        Printf.sprintf "assert (%s) as Hand by (%s)."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
          (apply (string_of_name f) l)
      in
      let str2 = Printf.sprintf "now inversion Hand." in
      Command str1 :: [ Command str2 ]
  | Ast.AndElimRight (p, q, prf) ->
      let str1 =
        Printf.sprintf "assert (%s) as Hand."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
      in
      let str2 = Printf.sprintf "now inversion Hand." in
      let strand = coq_string_step_of_proof prf ctx in
      [ Command str1; Step strand; Step [ Command str2 ] ]
  | Ast.AndElimLeft (p, q, prf) ->
      let str1 =
        Printf.sprintf "assert (%s) as Hand."
          (string_of_coq_prop
             (Conjonction (translate_proposition p, translate_proposition q)))
      in
      let str2 = Printf.sprintf "now inversion Hand." in
      let strand = coq_string_step_of_proof prf ctx in
      [ Command str1; Step strand; Step [ Command str2 ] ]
  | Ast.OrIntroL (_, _, prf) ->
      let str = coq_string_step_of_proof prf ctx in
      Command "left." :: str
  | Ast.OrIntroR (_, _, prf) ->
      let str = coq_string_step_of_proof prf ctx in
      Command "right." :: str
  | Ast.OrInd (_, _, _, hleft, proofleft, hright, proofright, Ast.Assumption x)
    ->
      let str1 = Printf.sprintf "inversion %s as [%s|%s]." x hleft hright in
      let strleft = coq_string_step_of_proof proofleft ctx in
      let strright = coq_string_step_of_proof proofright ctx in
      [ Command str1; Step strleft; Step strright ]
  | Ast.OrInd
      (_, _, _, hleft, proofleft, hright, proofright, Ast.GlobalAssumption x) ->
      let str1 =
        Printf.sprintf "destruct %s as [%s|%s]." (string_of_name x) hleft hright
      in
      let strleft = coq_string_step_of_proof proofleft ctx in
      let strright = coq_string_step_of_proof proofright ctx in
      [ Command str1; Step strleft; Step strright ]
  | Ast.OrInd (p, q, _, hleft, proofleft, hright, proofright, Ast.Apply (f, l))
    ->
      let str =
        Printf.sprintf "assert (%s) as %s by (%s)."
          (string_of_coq_prop
             (Disjonction (translate_proposition p, translate_proposition q)))
          hleft (apply f l)
      in
      let str1 = Printf.sprintf "inversion %s as [%s|%s]." hleft hleft hright in
      let strleft = coq_string_step_of_proof proofleft ctx in
      let strright = coq_string_step_of_proof proofright ctx in
      [ Command str; Command str1; Step strleft; Step strright ]
  | Ast.OrInd
      (p, q, _, hleft, proofleft, hright, proofright, Ast.ApplyTheorem (f, l))
    ->
      let str =
        Printf.sprintf "assert (%s) as %s by (%s)."
          (string_of_coq_prop
             (Disjonction (translate_proposition p, translate_proposition q)))
          hleft
          (apply (string_of_name f) l)
      in
      let str1 = Printf.sprintf "inversion %s as [%s|%s]." hleft hleft hright in
      let strleft = coq_string_step_of_proof proofleft ctx in
      let strright = coq_string_step_of_proof proofright ctx in
      [ Command str; Command str1; Step strleft; Step strright ]
  | Ast.OrInd (p, q, _, hleft, proofleft, hright, proofright, prf) ->
      let str =
        Printf.sprintf "assert (%s) as %s."
          (string_of_coq_prop
             (Disjonction (translate_proposition p, translate_proposition q)))
          hleft
      in
      let str1 = Printf.sprintf "inversion %s as [%s|%s]." hleft hleft hright in
      let strleft = coq_string_step_of_proof proofleft ctx in
      let strright = coq_string_step_of_proof proofright ctx in
      let strprf = coq_string_step_of_proof prf ctx in
      [
        Command str;
        Step strprf;
        Step [ Command str1; Step strleft; Step strright ];
      ]
  | Ast.ExIntro (_, x, prf) ->
      let str =
        Printf.sprintf "exists %s."
          (string_of_coq_element (translate_element x))
      in
      let str1 = coq_string_step_of_proof prf ctx in
      Command str :: str1
  | Ast.ExInd (_, _, Ast.Assumption x, wit_name, h, proof_p) ->
      let str = Printf.sprintf "inversion %s as [%s %s]." x wit_name h in
      let str1 = coq_string_step_of_proof proof_p ctx in
      Command str :: str1
  | Ast.ExInd (_, _, Ast.GlobalAssumption x, wit_name, h, proof_p) ->
      let str =
        Printf.sprintf "destruct %s as [%s %s]." (string_of_name x) wit_name h
      in
      let str1 = coq_string_step_of_proof proof_p ctx in
      Command str :: str1
  | Ast.ExInd (pred, _, Ast.Apply (f, l), wit_name, h, proof_p) ->
      let stror =
        Printf.sprintf "assert (%s) as %s by (%s)."
          (string_of_coq_prop (translate_proposition (Ast.Exists pred)))
          h (apply f l)
      in
      let str = Printf.sprintf "inversion %s as [%s %s]." h wit_name h in
      let str1 = coq_string_step_of_proof proof_p ctx in
      Command stror :: Command str :: str1
  | Ast.ExInd (pred, _, Ast.ApplyTheorem (f, l), wit_name, h, proof_p) ->
      let stror =
        Printf.sprintf "assert (%s) as %s by (%s)."
          (string_of_coq_prop (translate_proposition (Ast.Exists pred)))
          h
          (apply (string_of_name f) l)
      in
      let str = Printf.sprintf "inversion %s as [%s %s]." h wit_name h in
      let str1 = coq_string_step_of_proof proof_p ctx in
      Command stror :: Command str :: str1
  | Ast.ExInd (pred, _, prfexists, wit_name, h, proof_p) ->
      let stror =
        Printf.sprintf "assert (%s) as %s."
          (string_of_coq_prop (translate_proposition (Ast.Exists pred)))
          h
      in
      let str = Printf.sprintf "inversion %s as [%s %s]." h wit_name h in
      let str1 = coq_string_step_of_proof proof_p ctx in
      let strexists = coq_string_step_of_proof prfexists ctx in
      [ Command stror; Step strexists; Step (Command str :: str1) ]
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
  | Ast.Cut (_, Ast.Assumption _, _, _)
  | Ast.Cut (_, Ast.GlobalAssumption _, _, _) ->
      failwith "Should not happen."
  | Ast.Cut (p, Apply (f, l), h, prf) ->
      let strcut =
        Printf.sprintf "assert (%s) as %s by (%s)." (coq_string_of_prop p) h
          (apply f l)
      in
      let str = coq_string_step_of_proof prf ctx in
      Command strcut :: str
  | Ast.Cut (p, ApplyTheorem (f, l), h, prf) ->
      let strcut =
        Printf.sprintf "assert (%s) as %s by (%s)." (coq_string_of_prop p) h
          (apply (string_of_name f) l)
      in
      let str = coq_string_step_of_proof prf ctx in
      Command strcut :: str
  | Ast.Cut (p, prfp, h, prf) ->
      let strcut =
        Printf.sprintf "assert (%s) as %s." (coq_string_of_prop p) h
      in
      let strp = coq_string_step_of_proof prfp ctx in
      let str = coq_string_step_of_proof prf ctx in
      [ Command strcut; Step strp; Step str ]
  | Ast.Apply (th, args) ->
      let str = apply th args in
      [ Command (Printf.sprintf "%s." str) ]
  | Ast.ApplyTheorem (th, args) ->
      let str = apply (string_of_name th) args in
      [ Command (Printf.sprintf "%s." str) ]
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
      let y = translate_element y in
      let str =
        Printf.sprintf "transitivity %s."
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
      in
      Command str :: Step proof1 :: [ Step proof2 ]
  | Ast.EqElim ((set, id, pred), x, y, _, Assumption hprf, _, Assumption heq) ->
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command eqind ]
  | Ast.EqElim ((set, id, pred), x, y, _, Assumption hprf, heq, prfeq)
    when is_simply_cut prfeq ->
      let cuteq =
        Printf.sprintf "assert (%s = %s) as %s by (%s)."
          (string_of_coq_element (translate_element x))
          (string_of_coq_element (translate_element y))
          heq (simple_cut prfeq)
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cuteq; Command eqind ]
  | Ast.EqElim ((set, id, pred), x, y, _, Assumption hprf, heq, prfeq) ->
      let prfeq = coq_string_step_of_proof prfeq ctx in
      let cuteq =
        Printf.sprintf "assert (%s = %s) as %s."
          (string_of_coq_element (translate_element x))
          (string_of_coq_element (translate_element y))
          heq
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cuteq; Step prfeq; Step [ Command eqind ] ]
  | Ast.EqElim ((set, id, pred), x, y, hprf, prf, _, Assumption heq)
    when is_simply_cut prf ->
      let cut =
        Printf.sprintf "assert (%s) as %s by (%s)."
          (coq_string_of_prop (Ast.instantiate id pred x))
          hprf (simple_cut prf)
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cut; Command eqind ]
  | Ast.EqElim ((set, id, pred), x, y, hprf, prf, _, Assumption heq) ->
      let prf = coq_string_step_of_proof prf ctx in
      let cut =
        Printf.sprintf "assert (%s) as %s."
          (coq_string_of_prop (Ast.instantiate id pred x))
          hprf
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cut; Step prf; Step [ Command eqind ] ]
  | Ast.EqElim ((set, id, pred), x, y, hprf, prf, heq, prfeq)
    when is_simply_cut prf && is_simply_cut prfeq ->
      Printf.printf "Oui !";
      let cuteq =
        Printf.sprintf "assert (%s = %s) as %s by (%s)."
          (string_of_coq_element (translate_element x))
          (string_of_coq_element (translate_element y))
          heq (simple_cut prfeq)
      in
      let cut =
        Printf.sprintf "assert (%s) as %s by (%s)."
          (coq_string_of_prop (Ast.instantiate id pred x))
          hprf (simple_cut prf)
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cut; Command cuteq; Command eqind ]
  | Ast.EqElim ((set, id, pred), x, y, hprf, prf, heq, prfeq)
    when is_simply_cut prfeq ->
      Printf.printf "Oui !";
      let prf = coq_string_step_of_proof prf ctx in
      let cuteq =
        Printf.sprintf "assert (%s = %s) as %s by (%s)."
          (string_of_coq_element (translate_element x))
          (string_of_coq_element (translate_element y))
          heq (simple_cut prfeq)
      in
      let cut =
        Printf.sprintf "assert (%s) as %s."
          (coq_string_of_prop (Ast.instantiate id pred x))
          hprf
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cut; Step prf; Step [ Command cuteq; Command eqind ] ]
  | Ast.EqElim ((set, id, pred), x, y, hprf, prf, heq, prfeq)
    when is_simply_cut prf ->
      Printf.printf "Oui !";
      let prfeq = coq_string_step_of_proof prfeq ctx in
      let cuteq =
        Printf.sprintf "assert (%s = %s) as %s."
          (string_of_coq_element (translate_element x))
          (string_of_coq_element (translate_element y))
          heq
      in
      let cut =
        Printf.sprintf "assert (%s) as %s by (%s)."
          (coq_string_of_prop (Ast.instantiate id pred x))
          hprf (simple_cut prf)
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cut; Command cuteq; Step prfeq; Step [ Command eqind ] ]
  | Ast.EqElim ((set, id, pred), x, y, hprf, prf, heq, prfeq) ->
      let prf = coq_string_step_of_proof prf ctx in
      let prfeq = coq_string_step_of_proof prfeq ctx in
      let cuteq =
        Printf.sprintf "assert (%s = %s) as %s."
          (string_of_coq_element (translate_element x))
          (string_of_coq_element (translate_element y))
          heq
      in
      let cut =
        Printf.sprintf "assert (%s) as %s."
          (coq_string_of_prop (Ast.instantiate id pred x))
          hprf
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [
        Command cut;
        Step prf;
        Step [ Command cuteq; Step prfeq; Step [ Command eqind ] ];
      ]
  | Ast.EqElimR ((set, id, pred), x, y, _, Assumption hprf, _, Assumption heq)
    ->
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind_r %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command eqind ]
  | Ast.EqElimR ((set, id, pred), x, y, _, Assumption hprf, heq, prfeq)
    when is_simply_cut prfeq ->
      let cuteq =
        Printf.sprintf "assert (%s = %s) as %s by (%s)."
          (string_of_coq_element (translate_element y))
          (string_of_coq_element (translate_element x))
          heq (simple_cut prfeq)
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind_r %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cuteq; Command eqind ]
  | Ast.EqElimR ((set, id, pred), x, y, _, Assumption hprf, heq, prfeq) ->
      let prfeq = coq_string_step_of_proof prfeq ctx in
      let cuteq =
        Printf.sprintf "assert (%s = %s) as %s."
          (string_of_coq_element (translate_element y))
          (string_of_coq_element (translate_element x))
          heq
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind_r %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cuteq; Step prfeq; Step [ Command eqind ] ]
  | Ast.EqElimR ((set, id, pred), x, y, hprf, prf, _, Assumption heq)
    when is_simply_cut prf ->
      let cut =
        Printf.sprintf "assert (%s) as %s by (%s)."
          (coq_string_of_prop (Ast.instantiate id pred x))
          hprf (simple_cut prf)
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind_r %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cut; Command eqind ]
  | Ast.EqElimR ((set, id, pred), x, y, hprf, prf, _, Assumption heq) ->
      let prf = coq_string_step_of_proof prf ctx in
      let cut =
        Printf.sprintf "assert (%s) as %s."
          (coq_string_of_prop (Ast.instantiate id pred x))
          hprf
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind_r %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cut; Step prf; Step [ Command eqind ] ]
  | Ast.EqElimR ((set, id, pred), x, y, hprf, prf, heq, prfeq)
    when is_simply_cut prf && is_simply_cut prfeq ->
      Printf.printf "Oui !";
      let cuteq =
        Printf.sprintf "assert (%s = %s) as %s by (%s)."
          (string_of_coq_element (translate_element y))
          (string_of_coq_element (translate_element x))
          heq (simple_cut prfeq)
      in
      let cut =
        Printf.sprintf "assert (%s) as %s by (%s)."
          (coq_string_of_prop (Ast.instantiate id pred x))
          hprf (simple_cut prf)
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind_r %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cut; Command cuteq; Command eqind ]
  | Ast.EqElimR ((set, id, pred), x, y, hprf, prf, heq, prfeq)
    when is_simply_cut prfeq ->
      Printf.printf "Oui !";
      let prf = coq_string_step_of_proof prf ctx in
      let cuteq =
        Printf.sprintf "assert (%s = %s) as %s by (%s)."
          (string_of_coq_element (translate_element y))
          (string_of_coq_element (translate_element x))
          heq (simple_cut prfeq)
      in
      let cut =
        Printf.sprintf "assert (%s) as %s."
          (coq_string_of_prop (Ast.instantiate id pred x))
          hprf
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind_r %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cut; Step prf; Step [ Command cuteq; Command eqind ] ]
  | Ast.EqElimR ((set, id, pred), x, y, hprf, prf, heq, prfeq)
    when is_simply_cut prf ->
      Printf.printf "Oui !";
      let prfeq = coq_string_step_of_proof prfeq ctx in
      let cuteq =
        Printf.sprintf "assert (%s = %s) as %s."
          (string_of_coq_element (translate_element y))
          (string_of_coq_element (translate_element x))
          heq
      in
      let cut =
        Printf.sprintf "assert (%s) as %s by (%s)."
          (coq_string_of_prop (Ast.instantiate id pred x))
          hprf (simple_cut prf)
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind_r %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [ Command cut; Command cuteq; Step prfeq; Step [ Command eqind ] ]
  | Ast.EqElimR ((set, id, pred), x, y, hprf, prf, heq, prfeq) ->
      let prf = coq_string_step_of_proof prf ctx in
      let prfeq = coq_string_step_of_proof prfeq ctx in
      let cuteq =
        Printf.sprintf "assert (%s = %s) as %s."
          (string_of_coq_element (translate_element y))
          (string_of_coq_element (translate_element x))
          heq
      in
      let cut =
        Printf.sprintf "assert (%s) as %s."
          (coq_string_of_prop (Ast.instantiate id pred x))
          hprf
      in
      let x = translate_element x in
      let y = translate_element y in
      let eqind =
        Printf.sprintf "apply (@eq_ind_r %s %s (fun %s => %s) %s %s %s)."
          (string_of_name set)
          (string_with_or_without_par (string_of_coq_element x)
             (not (is_atomic_element x)))
          id (coq_string_of_prop pred) hprf
          (string_with_or_without_par (string_of_coq_element y)
             (not (is_atomic_element y)))
          heq
      in
      [
        Command cut;
        Step prf;
        Step [ Command cuteq; Step prfeq; Step [ Command eqind ] ];
      ]

let string_of_coq_proof proof =
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
        (string_of_coq_prop (translate_proposition prop))
  | (_, f), Ast.Predicate (args, prop) ->
      Printf.sprintf "Definition %s%s := %s." f
        (string_of_args args false)
        (string_of_coq_prop (translate_proposition prop))
  | (_, f), Ast.Function (args, _, te) ->
      Printf.sprintf "Definition %s%s := %s." f
        (string_of_args args false)
        (string_of_coq_element (translate_element te))
  | (_, p), Ast.Theorem (prop, proof) ->
      Printf.sprintf "Theorem %s: %s.%s\nQed." p
        (string_of_coq_prop (translate_proposition prop))
        (string_of_coq_proof (translate_proof (Proof.simplify_proof proof)))

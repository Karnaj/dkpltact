let string_of_name f = if fst f = "" then snd f else (fst f) ^ "." ^ (snd f)


let string_of_decl decl = match decl with
| Ast.SetDecl(s) -> Printf.sprintf "%s: plth.Set." s 
| Ast.ElementDecl(x, set) -> Printf.sprintf "%s: plth.El %s." x (string_of_name set)
| _ -> Printf.sprintf ""
(*
| Ast.FunctionDecl(f, args, ret) -> Printf.sprintf "%s: plth.function (%s)." f (string_of_paramaters_type args) (string_of_name ret) 
| Ast.PredicateDecl(f, args) -> Printf.sprintf "Definition %s: %s -> Prop." f (string_of_paramaters_type args)
| Ast.AxiomDecl(p, prop) -> Printf.sprintf "Axiom %s: %s" p (string_of_coq_prop (translate_proposition prop))
| Ast.PredicateDef(f, args, prop) -> Printf.sprintf "Definition %s%s := %s." f (string_of_args args false) (string_of_coq_prop (translate_proposition prop))
| Ast.FunctionDef(f, args, _, te) -> Printf.sprintf "Definition %s%s:= %s." f (string_of_args args false) (string_of_coq_element (translate_element te))
| Ast.TheoremDef(p, prop, _) -> Printf.sprintf "Theorem %s: %s" p (string_of_coq_prop (translate_proposition prop))
*)
let rec replace_var_in_term x t = function 
  | Ast.TElement(x) -> Ast.TElement(x)
  | Ast.TProof(p) -> Ast.TProof(replace_var x t p)

and replace_var x t = function
| Ast.T -> Ast.T
| Ast.FalseElim(prf) -> Ast.FalseElim(replace_var x t prf)
| Ast.Assumption(y) when x = y -> t
| Ast.Assumption(y) -> Ast.Assumption(y)
| Ast.GlobalAssumption(y) -> Ast.GlobalAssumption(y)
| Ast.AndIntro(p, q, prfp, prfq) -> Ast.AndIntro(p, q, replace_var x t prfp, replace_var x t prfq)
| Ast.AndInd(hp, p, hq, q, prfand, r, prf) -> Ast.AndInd(hp, p, hq, q, replace_var x t prfand, r, replace_var x t  prf)
| Ast.AndIndLeft(hp, p, q, prfand, r, prf) -> Ast.AndIndLeft(hp, p, q, replace_var x t prfand, r, replace_var x t  prf)
| Ast.AndIndRight(p, hq, q, prfand, r, prf) -> Ast.AndIndRight(p, hq, q, replace_var x t prfand, r, replace_var x t  prf)
| Ast.AndElimLeft(p, q, prf) -> Ast.AndElimLeft(p, q, replace_var x t  prf)
| Ast.AndElimRight(p, q, prf) -> Ast.AndElimRight(p, q, replace_var x t prf)
| Ast.OrIntroL(p, q, prf) -> OrIntroL(p, q, replace_var x t prf)
| Ast.OrIntroR(p, q, prf) -> OrIntroR(p, q, replace_var x t prf)
| Ast.OrInd(p, q, r, h1, p1, h2, p2, prf) -> Ast.OrInd(p, q, r, h1, replace_var x t p1, h2, replace_var x t p2, replace_var x t  prf)
| ExIntro(pred, e, prf) -> ExIntro(pred, e, replace_var x t  prf)
| ForallIntro(pred, prf) -> ForallIntro(pred, replace_var x t prf)
| ForallElim(pred, prf, e) -> ForallElim(pred, replace_var x t prf, e)
| ImplIntro(h, p, prfp) -> ImplIntro(h, p, replace_var x t prfp)
| Ast.Apply(f, l) when f = x -> 
    begin match t with 
      | Ast.Assumption(y) -> Ast.Apply(y, List.map (replace_var_in_term x t) l)
      | Ast.GlobalAssumption(y) -> Ast.ApplyTheorem(y, List.map (replace_var_in_term x t) l)
      | _ -> failwith "Nope"
    end
| Ast.Apply(f, l) -> Ast.Apply(f, List.map (replace_var_in_term x t) l)
| Ast.ApplyTheorem(f, l) -> Ast.ApplyTheorem(f, List.map (replace_var_in_term x t) l)
| _ -> failwith "TODO"
(*
  | ExIntro of predicate * element * proof 
  | ExInd of predicate * proposition * proof * variable * variable * proof
  | ForallIntro of predicate * proof
  | ForallElim of predicate * proof * element
  | ImplIntro of variable * proposition * proof 
  | ImplElim of variable * proposition * proof * proof (* (H, A, Pimp, PA) Show A => B as H, and show A.*)
  | Cut of proposition * proof * variable * proof
  | NNPP of proposition * proof
  | EqElim of predicate * element * element * proof * proof
  | EqElimR of predicate * element * element * proof * proof
  | EqSym of name * element * element * proof
  | EqRefl of name * element 
  | EqTrans of name * element * element * element * proof * proof 
  | Apply of variable * term list (* Use another theorem, replace it by ImplElim and ForallElim. *)
  | ApplyTheorem of name * term list
| OrElim -> TODO
| ExElim  -> TODO
| ImplElim -> TODO
| AndElim(x, ) -> TODO
| Cut of proposition * proof * variable * proof
| NNPP of proposition * proof
| EqElim of predicate * term * term * proof * proof
| EqElimR of predicate * term * term * proof * proof
| EqSym of predicate * term * term * proof * proof
| EqRefl of predicate * term * term * proof * proof 
| EqTrans of predicate * term * term * term * proof * proof * proof   
*) 



let rec simplify_proof p = match p with
  | Ast.Cut(_, Ast.Assumption(v), x, prf) -> 
      replace_var x (Ast.Assumption(v)) (simplify_proof prf)
  | Ast.Cut(_, Ast.GlobalAssumption(v), x, prf) -> 
    let _ = Printf.printf "BOOM %s -> %s" x (snd v) in
    replace_var x (Ast.GlobalAssumption(v)) (simplify_proof prf)
  | t -> t

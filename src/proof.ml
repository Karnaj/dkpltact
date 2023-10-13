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
| Ast.AndInd(hp, p, hq, q, prfand, r, prf) -> 
    let prf = if hp = x || hq = x then prf else replace_var x t prf in 
    Ast.AndInd(hp, p, hq, q, prfand, r, prf)
| Ast.AndIndLeft(hp, p, q, prfand, r, prf) -> 
    let prf = if hp = x then prf else replace_var x t prf in 
    Ast.AndIndLeft(hp, p, q, replace_var x t prfand, r, prf)
| Ast.AndIndRight(p, hq, q, prfand, r, prf) -> 
    let prf = if hq = x then prf else replace_var x t prf in 
    Ast.AndIndRight(p, hq, q, replace_var x t prfand, r, prf)
| Ast.AndElimLeft(p, q, prf) -> Ast.AndElimLeft(p, q, replace_var x t  prf)
| Ast.AndElimRight(p, q, prf) -> Ast.AndElimRight(p, q, replace_var x t prf)
| Ast.OrIntroL(p, q, prf) -> OrIntroL(p, q, replace_var x t prf)
| Ast.OrIntroR(p, q, prf) -> OrIntroR(p, q, replace_var x t prf)

| Ast.OrInd(p, q, r, h1, p1, h2, p2, prfor) -> 
    let p1 = if h1 = x then p1 else replace_var x t p1 in 
    let p2 = if h2 = x then p2 else replace_var x t p2 in 
    Ast.OrInd(p, q, r, h1, p1, h2, p2, replace_var x t  prfor)
| Ast.ExIntro(pred, e, prf) -> Ast.ExIntro(pred, e, replace_var x t prf)
| Ast.ExInd(pred, p, prfex, x, h, prf) -> 
    let prf = if h = x then prf else replace_var x t prf in 
    Ast.ExInd(pred, p, replace_var x t prfex, x, h, prf)
| Ast.ForallIntro(pred, prf) -> Ast.ForallIntro(pred, replace_var x t prf)
| Ast.ForallElim(pred, prf, e) -> Ast.ForallElim(pred, replace_var x t prf, e)
| Ast.ImplIntro(h, p, prf) -> 
  let prf = if h = x then prf else replace_var x t prf in 
    Ast.ImplIntro(h, p, replace_var x t prf)
| Ast.ImplElim(h, p, prfimp, prf) -> 
    let prf = if h = x then prf else replace_var x t prf in 
    Ast.ImplElim(h, p, prfimp, replace_var x t prf)
| Ast.Cut(p, prfp, h, prf) -> 
  let prf = if h = x then prf else replace_var x t prf in   
    Ast.Cut(p, prfp, h, prf)
| Ast.NNPP(p, prf) -> Ast.NNPP(p, replace_var x t prf)
| Ast.EqElim(pred, y, z, prfeq, prf) -> 
    Ast.EqElim(pred, y, z, replace_var x t prfeq, replace_var x t prf)
| Ast.EqElimR(pred, y, z, prfeq, prf) -> 
    Ast.EqElimR(pred, y, z, replace_var x t prfeq, replace_var x t prf) 
| Ast.EqSym(set, y, z, prf) -> Ast.EqSym(set, y, z, replace_var x t prf) 
| Ast.EqRefl(set, y) -> Ast.EqRefl(set, y) 
| Ast.EqTrans(set, u, v, w, prf1, prf2) -> 
  Ast.EqTrans(set, u, v, w, replace_var x t prf1, replace_var x t prf2) 
| Ast.Apply(f, l) when f = x -> 
    begin match t with 
      | Ast.Assumption(y) -> Ast.Apply(y, List.map (replace_var_in_term x t) l)
      | Ast.GlobalAssumption(y) -> Ast.ApplyTheorem(y, List.map (replace_var_in_term x t) l)
      | _ -> failwith "Nope"
    end
| Ast.Apply(f, l) -> Ast.Apply(f, List.map (replace_var_in_term x t) l)
| Ast.ApplyTheorem(f, l) -> Ast.ApplyTheorem(f, List.map (replace_var_in_term x t) l)
(*

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
*) 



let rec simplify_proof p = match p with
  | Ast.Cut(_, Ast.Assumption(v), x, prf) -> 
      replace_var x (Ast.Assumption(v)) (simplify_proof prf)
  | Ast.Cut(_, Ast.GlobalAssumption(v), x, prf) -> 
    replace_var x (Ast.GlobalAssumption(v)) (simplify_proof prf)
  | t -> t

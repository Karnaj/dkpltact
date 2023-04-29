
let rec simplify_proof p = match p with
  | Cut(_, Assumption(v), x, prf) -> replace x (Assumption(v)) (simplify_proof prf)
  | Cut(_, GlobalAssumption(v), x, prf) -> replace x (GlobalAssumption(v)) (simplify_proof prf)


let rec replace_var x t = function
| T -> T
| FalseElim -> t
| Assumption(y) when x = y -> y
| Assumption(y) -> Assumption(y)
| GlobalAssumption(y) -> GlobalAssumption(y)
| AndIntro(p, q, prfp, prfq) --> AndIntro(p, q, replace_var x t prfp, replace_var x t prfq)
| OrIntroL(p, q, prf) --> OrIntroL(p, q, replace_var x t prf)
| OrIntroR(p, q, prf) --> OrIntroR(p, q, replace_var x t prf)
| ExIntro(pred, e, prf) -> ExIntro(pred, e, prf)
| ForallIntro(pred, prf) -> ForallIntro(pred, replace_var x t prf)
| ForallElim(pred, prf, e) -> ForallElim(pred, replace_var x t prf, e)
| ImplIntro(p, prfp, prfq) --> ImplIntro(p, replace_var x t prfp, replace_var x t prfq)
| Apply(f, l) -> Apply(f, replace_var_in_term x t l)
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
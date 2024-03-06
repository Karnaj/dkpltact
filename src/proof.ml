(** Replace a local hypothesis by another hypothesis.
**)

let replace_var_in_term (x : Ast.variable) (prf : Ast.assertion) (t : Ast.term)
    : Ast.term =
  match t with
  | Ast.TAssertion (Ast.LocalAssertion y) when x = y -> Ast.TAssertion prf
  | term -> term

let replace_var_in_assertion (x : Ast.variable) (t : Ast.assertion)
    (h : Ast.assertion) =
  match h with LocalAssertion y when x = y -> t | _ -> h

let rec replace_var (x : Ast.variable) (t : Ast.assertion) = function
  | Ast.T -> Ast.T
  | Ast.FalseElim prf -> Ast.FalseElim (replace_var x t prf)
  | Ast.Assumption (Ast.LocalAssertion y) when x = y -> Ast.Assumption t
  | Ast.Assumption y -> Ast.Assumption y
  | Ast.AndIntro (p, q, prfp, prfq) ->
      Ast.AndIntro (p, q, replace_var x t prfp, replace_var x t prfq)
  | Ast.OrIntroL (p, q, prf) -> OrIntroL (p, q, replace_var x t prf)
  | Ast.OrIntroR (p, q, prf) -> OrIntroR (p, q, replace_var x t prf)
  | Ast.ExIntro (pred, e, prf) -> Ast.ExIntro (pred, e, replace_var x t prf)
  | Ast.ForallIntro (pred, prf) -> Ast.ForallIntro (pred, replace_var x t prf)
  | Ast.ImplIntro (h, p, prf) ->
      let prf = if h = x then prf else replace_var x t prf in
      Ast.ImplIntro (h, p, replace_var x t prf)
  | Ast.AndInd (p, q, prfand, r, hp, hq, prf) ->
      let prf = if hp = x || hq = x then prf else replace_var x t prf in
      let prfand = replace_var_in_assertion x t prfand in
      Ast.AndInd (p, q, prfand, r, hp, hq, prf)
  | Ast.AndIndRight (p, q, prfand, r, hp, prf) ->
      let prf = if hp = x then prf else replace_var x t prf in
      let prfand = replace_var_in_assertion x t prfand in
      Ast.AndIndRight (p, q, prfand, r, hp, prf)
  | Ast.AndIndLeft (p, q, prfand, r, hq, prf) ->
      let prf = if hq = x then prf else replace_var x t prf in
      let prfand = replace_var_in_assertion x t prfand in
      Ast.AndIndLeft (p, q, prfand, r, hq, prf)
  | Ast.AndElimLeft (p, q, prf) ->
      Ast.AndElimLeft (p, q, replace_var_in_assertion x t prf)
  | Ast.AndElimRight (p, q, prf) ->
      Ast.AndElimRight (p, q, replace_var_in_assertion x t prf)
  | Ast.OrInd (p, q, prfor, r, h1, prf1, h2, prf2) ->
      let prf1 = if h1 = x then prf1 else replace_var x t prf1 in
      let prf2 = if h2 = x then prf2 else replace_var x t prf2 in
      let prfor = replace_var_in_assertion x t prfor in
      Ast.OrInd (p, q, prfor, r, h1, prf1, h2, prf2)
  | Ast.ExInd (abs, prfex, r, wit, h, prf) ->
      let prf = if h = x || wit = x then prf else replace_var x t prf in
      let prfex = replace_var_in_assertion x t prfex in
      Ast.ExInd (abs, prfex, r, wit, h, prf)
  | Ast.ForallElim (abs, prf, e) -> Ast.ForallElim (abs, replace_var x t prf, e)
  | Ast.ImplElim (h, p, prfimp, prf) ->
      let prf = if h = x then prf else replace_var x t prf in
      Ast.ImplElim (h, p, replace_var x t prfimp, prf)
  | Ast.Cut (p, prfp, h, prf) ->
      let prf = if h = x then prf else replace_var x t prf in
      let prfp = replace_var x t prfp in
      Ast.Cut (p, prfp, h, prf)
  | Ast.NNPP (p, prf) -> Ast.NNPP (p, replace_var x t prf)
  | Ast.EqElim (abs, y, z, hprf, heq) ->
      Ast.EqElim
        ( abs,
          y,
          z,
          replace_var_in_assertion x t hprf,
          replace_var_in_assertion x t heq )
  | Ast.EqElimR (abs, y, z, hprf, heq) ->
      Ast.EqElimR
        ( abs,
          y,
          z,
          replace_var_in_assertion x t hprf,
          replace_var_in_assertion x t heq )
  | Ast.EqSym (set, y, z, prf) -> Ast.EqSym (set, y, z, replace_var x t prf)
  | Ast.EqRefl (set, y) -> Ast.EqRefl (set, y)
  | Ast.EqTrans (set, u, v, w, prf1, prf2) ->
      Ast.EqTrans (set, u, v, w, replace_var x t prf1, replace_var x t prf2)
  | Ast.Apply (f, l) ->
      Ast.Apply
        (replace_var_in_assertion x t f, List.map (replace_var_in_term x t) l)
  | Ast.Classic p -> Ast.Classic p

let rec simplify_proof (prf : Ast.proof) : Ast.proof =
  match prf with
  | Ast.T -> Ast.T
  | Ast.FalseElim prf -> Ast.FalseElim (simplify_proof prf)
  | Ast.Assumption y -> Ast.Assumption y
  | Ast.AndIntro (p, q, prfp, prfq) ->
      Ast.AndIntro (p, q, simplify_proof prfp, simplify_proof prfq)
  | Ast.OrIntroL (p, q, prf) -> OrIntroL (p, q, simplify_proof prf)
  | Ast.OrIntroR (p, q, prf) -> OrIntroR (p, q, simplify_proof prf)
  | Ast.ExIntro (abs, e, prf) -> Ast.ExIntro (abs, e, simplify_proof prf)
  | Ast.ForallIntro (abs, prf) -> Ast.ForallIntro (abs, simplify_proof prf)
  | Ast.ImplIntro (h, p, prf) -> Ast.ImplIntro (h, p, simplify_proof prf)
  | Ast.AndInd (p, q, h, r, hp, hq, prf) ->
      Ast.AndInd (p, q, h, r, hp, hq, simplify_proof prf)
  | Ast.AndIndRight (p, q, h, r, hp, prf) ->
      Ast.AndIndRight (p, q, h, r, hp, simplify_proof prf)
  | Ast.AndIndLeft (p, q, h, r, hq, prf) ->
      Ast.AndIndLeft (p, q, h, r, hq, simplify_proof prf)
  | Ast.AndElimRight (_, _, _) -> prf
  | Ast.AndElimLeft (_, _, _) -> prf
  | Ast.OrInd (p, q, h, r, hp, prfp, hq, prfq) ->
      Ast.OrInd (p, q, h, r, hp, simplify_proof prfp, hq, simplify_proof prfq)
  | Ast.ExInd (abs, h, r, wit, hp, prf) ->
      Ast.ExInd (abs, h, r, wit, hp, simplify_proof prf)
  | Ast.ForallElim (abs, prf, e) -> Ast.ForallElim (abs, simplify_proof prf, e)
  | Ast.ImplElim (h, p, prfimp, prf) ->
      Ast.ImplElim (h, p, simplify_proof prfimp, simplify_proof prf)
  | Ast.NNPP (p, prf) -> Ast.NNPP (p, simplify_proof prf)
  | Ast.Classic p -> Ast.Classic p
  | Ast.EqElim (_, _, _, _, _) -> prf
  | Ast.EqElimR (_, _, _, _, _) -> prf
  | Ast.EqSym (set, y, z, prf) -> Ast.EqSym (set, y, z, simplify_proof prf)
  | Ast.EqRefl (set, y) -> Ast.EqRefl (set, y)
  | Ast.EqTrans (set, u, v, w, prf1, prf2) ->
      Ast.EqTrans (set, u, v, w, simplify_proof prf1, simplify_proof prf2)
  | Ast.Apply (_, _) -> prf
  | Ast.Cut (_, Ast.Assumption v, x, prf) ->
      replace_var x v (simplify_proof prf)
  | Ast.Cut (_, prfp, h, Ast.Assumption (LocalAssertion h1)) when h = h1 -> prfp
  | Ast.Cut (p, prfp, h, prf) ->
      Ast.Cut (p, simplify_proof prfp, h, simplify_proof prf)

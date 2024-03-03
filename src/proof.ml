let rec replace_var_in_term x t = function
  | Ast.TElement x -> Ast.TElement x
  | Ast.TProof p -> Ast.TProof (replace_var x t p)

and replace_var x t = function
  | Ast.T -> Ast.T
  | Ast.FalseElim prf -> Ast.FalseElim (replace_var x t prf)
  | Ast.Assumption y when x = y -> t
  | Ast.Assumption y -> Ast.Assumption y
  | Ast.GlobalAssumption y -> Ast.GlobalAssumption y
  | Ast.AndIntro (p, q, prfp, prfq) ->
      Ast.AndIntro (p, q, replace_var x t prfp, replace_var x t prfq)
  | Ast.AndInd (hp, p, hq, q, prfand, r, prf) ->
      let prf = if hp = x || hq = x then prf else replace_var x t prf in
      Ast.AndInd (hp, p, hq, q, replace_var x t prfand, r, prf)
  | Ast.AndIndLeft (hp, p, q, prfand, r, prf) ->
      let prf = if hp = x then prf else replace_var x t prf in
      Ast.AndIndLeft (hp, p, q, replace_var x t prfand, r, prf)
  | Ast.AndIndRight (p, hq, q, prfand, r, prf) ->
      let prf = if hq = x then prf else replace_var x t prf in
      Ast.AndIndRight (p, hq, q, replace_var x t prfand, r, prf)
  | Ast.AndElimLeft (p, q, prf) -> Ast.AndElimLeft (p, q, replace_var x t prf)
  | Ast.AndElimRight (p, q, prf) -> Ast.AndElimRight (p, q, replace_var x t prf)
  | Ast.OrIntroL (p, q, prf) -> OrIntroL (p, q, replace_var x t prf)
  | Ast.OrIntroR (p, q, prf) -> OrIntroR (p, q, replace_var x t prf)
  | Ast.OrInd (p, q, r, h1, p1, h2, p2, prfor) ->
      let p1 = if h1 = x then p1 else replace_var x t p1 in
      let p2 = if h2 = x then p2 else replace_var x t p2 in
      Ast.OrInd (p, q, r, h1, p1, h2, p2, replace_var x t prfor)
  | Ast.ExIntro (pred, e, prf) -> Ast.ExIntro (pred, e, replace_var x t prf)
  | Ast.ExInd (pred, p, prfex, x, h, prf) ->
      let prf = if h = x then prf else replace_var x t prf in
      Ast.ExInd (pred, p, replace_var x t prfex, x, h, prf)
  | Ast.ForallIntro (pred, prf) -> Ast.ForallIntro (pred, replace_var x t prf)
  | Ast.ForallElim (pred, prf, e) ->
      Ast.ForallElim (pred, replace_var x t prf, e)
  | Ast.ImplIntro (h, p, prf) ->
      let prf = if h = x then prf else replace_var x t prf in
      Ast.ImplIntro (h, p, replace_var x t prf)
  | Ast.ImplElim (h, p, prfimp, prf) ->
      let prf = if h = x then prf else replace_var x t prf in
      Ast.ImplElim (h, p, prfimp, replace_var x t prf)
  | Ast.Cut (p, prfp, h, prf) ->
      let prf = if h = x then prf else replace_var x t prf in
      let prfp = replace_var x t prfp in
      Ast.Cut (p, prfp, h, prf)
  | Ast.NNPP (p, prf) -> Ast.NNPP (p, replace_var x t prf)
  | Ast.EqElim (pred, y, z, hprf, prfeq, heq, prf) ->
      Ast.EqElim
        (pred, y, z, hprf, replace_var x t prfeq, heq, replace_var x t prf)
  | Ast.EqElimR (pred, y, z, hprf, prfeq, heq, prf) ->
      Ast.EqElimR
        (pred, y, z, hprf, replace_var x t prfeq, heq, replace_var x t prf)
  | Ast.EqSym (set, y, z, prf) -> Ast.EqSym (set, y, z, replace_var x t prf)
  | Ast.EqRefl (set, y) -> Ast.EqRefl (set, y)
  | Ast.EqTrans (set, u, v, w, prf1, prf2) ->
      Ast.EqTrans (set, u, v, w, replace_var x t prf1, replace_var x t prf2)
  | Ast.Apply (f, l) when f = x -> (
      match t with
      | Ast.Assumption y -> Ast.Apply (y, List.map (replace_var_in_term x t) l)
      | Ast.GlobalAssumption y ->
          Ast.ApplyTheorem (y, List.map (replace_var_in_term x t) l)
      | _ -> failwith "Nope")
  | Ast.Apply (f, l) -> Ast.Apply (f, List.map (replace_var_in_term x t) l)
  | Ast.ApplyTheorem (f, l) ->
      Ast.ApplyTheorem (f, List.map (replace_var_in_term x t) l)
  | Ast.Classic p -> Ast.Classic p

let rec simplify_in_term = function
  | Ast.TElement x -> Ast.TElement x
  | Ast.TProof p -> Ast.TProof (simplify_proof p)

and simplify_proof p =
  match p with
  | Ast.T -> Ast.T
  | Ast.FalseElim prf -> Ast.FalseElim (simplify_proof prf)
  | Ast.Assumption y -> Ast.Assumption y
  | Ast.GlobalAssumption y -> Ast.GlobalAssumption y
  | Ast.AndIntro (p, q, prfp, prfq) ->
      Ast.AndIntro (p, q, simplify_proof prfp, simplify_proof prfq)
  | Ast.AndInd (hp, p, hq, q, prfand, r, prf) ->
      Ast.AndInd (hp, p, hq, q, simplify_proof prfand, r, simplify_proof prf)
  | Ast.AndIndLeft (hp, p, q, prfand, r, prf) ->
      Ast.AndIndLeft (hp, p, q, simplify_proof prfand, r, simplify_proof prf)
  | Ast.AndIndRight (p, hq, q, prfand, r, prf) ->
      Ast.AndIndRight (p, hq, q, simplify_proof prfand, r, prf)
  | Ast.AndElimLeft (p, q, prf) -> Ast.AndElimLeft (p, q, simplify_proof prf)
  | Ast.AndElimRight (p, q, prf) -> Ast.AndElimRight (p, q, simplify_proof prf)
  | Ast.OrIntroL (p, q, prf) -> OrIntroL (p, q, simplify_proof prf)
  | Ast.OrIntroR (p, q, prf) -> OrIntroR (p, q, simplify_proof prf)
  | Ast.OrInd (p, q, r, h1, p1, h2, p2, prfor) ->
      Ast.OrInd
        ( p,
          q,
          r,
          h1,
          simplify_proof p1,
          h2,
          simplify_proof p2,
          simplify_proof prfor )
  | Ast.ExIntro (pred, e, prf) -> Ast.ExIntro (pred, e, simplify_proof prf)
  | Ast.ExInd (pred, p, prfex, x, h, prf) ->
      Ast.ExInd (pred, p, simplify_proof prfex, x, h, simplify_proof prf)
  | Ast.ForallIntro (pred, prf) -> Ast.ForallIntro (pred, simplify_proof prf)
  | Ast.ForallElim (pred, prf, e) -> Ast.ForallElim (pred, simplify_proof prf, e)
  | Ast.ImplIntro (h, p, prf) -> Ast.ImplIntro (h, p, simplify_proof prf)
  | Ast.ImplElim (h, p, prfimp, prf) ->
      Ast.ImplElim (h, p, simplify_proof prfimp, simplify_proof prf)
  | Ast.NNPP (p, prf) -> Ast.NNPP (p, simplify_proof prf)
  | Ast.EqElim (pred, y, z, hprf, prfeq, heq, prf) ->
      Ast.EqElim
        (pred, y, z, hprf, simplify_proof prfeq, heq, simplify_proof prf)
  | Ast.EqElimR (pred, y, z, hprf, prfeq, heq, prf) ->
      Ast.EqElimR
        (pred, y, z, hprf, simplify_proof prfeq, heq, simplify_proof prf)
  | Ast.EqSym (set, y, z, prf) -> Ast.EqSym (set, y, z, simplify_proof prf)
  | Ast.EqRefl (set, y) -> Ast.EqRefl (set, y)
  | Ast.EqTrans (set, u, v, w, prf1, prf2) ->
      Ast.EqTrans (set, u, v, w, simplify_proof prf1, simplify_proof prf2)
  | Ast.Apply (f, l) -> Ast.Apply (f, List.map simplify_in_term l)
  | Ast.ApplyTheorem (f, l) -> Ast.ApplyTheorem (f, List.map simplify_in_term l)
  | Ast.Cut (_, Ast.Assumption v, x, prf) ->
      replace_var x (Ast.Assumption v) (simplify_proof prf)
  | Ast.Cut (_, Ast.GlobalAssumption v, x, prf) ->
      replace_var x (Ast.GlobalAssumption v) (simplify_proof prf)
  | Ast.Cut (_, prfp, h, Ast.Assumption h1) when h = h1 -> prfp
  | Ast.Cut (p, prfp, h, prf) ->
      Ast.Cut (p, simplify_proof prfp, h, simplify_proof prf)
  | Ast.Classic p -> Ast.Classic p

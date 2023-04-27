open Extras
open Kernel.Basic
open Kernel.Term
open Parsers.Entry
open Kernel.Rule

(** {1 Dedukti dependency computation} *)

let add_dep : mident -> StrSet.t =
 fun md -> StrSet.singleton (string_of_mident @@ md)

let qset_of_list f l =
  List.fold_left (fun set x -> StrSet.union (f x) set) StrSet.empty l

(** Term / pattern / entry traversal commands. *)

let rec mk_term t =
  match t with
  | Kind | Type _ | DB _ -> StrSet.empty
  | Const (_, c) -> add_dep (md c)
  | App (f, a, args) -> qset_of_list mk_term (f :: a :: args)
  | Lam (_, _, None, te) -> mk_term te
  | Lam (_, _, Some ty, te) -> StrSet.union (mk_term ty) (mk_term te)
  | Pi (_, _, a, b) -> StrSet.union (mk_term a) (mk_term b)

let rec mk_pattern p =
  match p with
  | Var (_, _, _, args) -> qset_of_list mk_pattern args
  | Pattern (_, c, args) ->
      StrSet.union (add_dep (md c)) (qset_of_list mk_pattern args)
  | Lambda (_, _, te) -> mk_pattern te
  | Brackets t -> mk_term t

let mk_rule r = StrSet.union (mk_pattern r.pat) (mk_term r.rhs)

let dep_of_entry = function
  | Decl (_, _, _, _, te) -> mk_term te
  | Def (_, _, _, _, None, te) -> mk_term te
  | Def (_, _, _, _, Some ty, te) -> StrSet.union (mk_term ty) (mk_term te)
  | Rules (_, rs) -> qset_of_list mk_rule rs
  | Eval (_, _, te) -> mk_term te
  | Infer (_, _, te) -> mk_term te
  | Check (_, _, _, Convert (t1, t2)) -> StrSet.union (mk_term t1) (mk_term t2)
  | Check (_, _, _, HasType (te, ty)) -> StrSet.union (mk_term te) (mk_term ty)
  | DTree (_, _, _) -> StrSet.empty
  | Print (_, _) -> StrSet.empty
  | Name (_, _) -> StrSet.empty
  | Require (_, md) -> add_dep md

let dep_of_entry (mds : mident list) e =
  List.fold_left
    (fun qset md -> StrSet.remove (string_of_mident md) qset)
    (dep_of_entry e) mds

let deps_of_md md =
  let files = List.map Api.Files.get_file md in
  let htbl = Api.Processor.handle_files files Api.Processor.Dependencies in
  Hashtbl.fold
    (fun _ { Api.Dep.deps; _ } acc -> Kernel.Basic.MidentSet.union acc deps)
    htbl Kernel.Basic.MidentSet.empty

let deps_of_md ?(transitive = false) md =
  if not transitive then deps_of_md [ md ]
  else
    (* Holds the result *)
    let depr = ref MidentSet.empty in
    (* Modules whose dependencies have been computed *)
    let comp = ref MidentSet.empty in
    let rec loop mds =
      if MidentSet.is_empty mds then ()
      else
        let m = MidentSet.choose mds in
        let mds = MidentSet.remove m mds in
        (* Dependencies of [m] are being computed. *)
        comp := MidentSet.add m !comp;
        let deps = deps_of_md [ m ] in
        depr := MidentSet.union !depr deps;
        (* Don't recompute values that have already been computed *)
        let deps = MidentSet.diff deps !comp in
        loop (MidentSet.union mds deps)
    in
    loop (MidentSet.singleton md);
    !depr

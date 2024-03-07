module Files = Api.Files
module P = Parsers.Parser

let test file out ctx entry : Ast._global_context =
  let name, entry = Parse.parse_entry file ctx entry in
  Printf.fprintf out "%s\n\n" (Coq.string_of_decl (name, entry));
  match entry with
  | Ast.Set -> Ast.declare_global_set name ctx
  | Ast.Axiom statement | Ast.Theorem (statement, _) ->
      Ast.declare_global_hypothesis name statement ctx
  | Ast.Element set -> Ast.declare_global_element name set ctx
  | Ast.PredicateSymbol args_types ->
      Ast.declare_global_predicate name args_types ctx
  | Ast.Predicate (args, prop) -> Ast.define_global_predicate name args prop ctx
  | Ast.FunctionSymbol (args_type, ret) ->
      Ast.declare_global_function name args_type ret ctx
  | Ast.Function (args, ret, el) ->
      Ast.define_global_function name args ret el ctx

let print_deps out deps =
  List.iter (Printf.fprintf out "Require Import %s.\n") deps;
  Printf.fprintf out "Require Import Coq.Logic.Classical_Prop.\n\n"

let parse_file folder ctx file deps =
  let oc = open_out ("output/" ^ file ^ ".v") in
  Printf.printf "\nWe are parsing %s.\n%!" file;
  let entries = P.(parse (input_from_file (folder ^ file ^ ".dk"))) in
  print_deps oc deps;
  let ctx = List.fold_left (test file oc) ctx entries in
  Printf.printf "Finish with %s.\n%!" file;
  close_out oc;
  ctx

let dep_of_file folder file =
  let entries = P.(parse (input_from_file (folder ^ file ^ ".dk"))) in
  let deps =
    List.fold_left
      (fun qset e -> Extras.StrSet.union qset (Deps.dep_of_entry [] e))
      Extras.StrSet.empty entries
  in
  Extras.StrSet.elements deps

let rec parse_module folder dones_and_ctx file =
  let dones, ctx = dones_and_ctx in
  if List.mem file dones then (dones, ctx)
  else
    let deps = dep_of_file folder file in
    let deps_files =
      List.filter
        (fun x ->
          x <> "plth" && x <> "logic" && x <> file && not (List.mem x dones))
        deps
    in
    let dones = file :: dones in
    let dones, ctx =
      List.fold_left (parse_module folder) (dones, ctx) deps_files
    in
    let ctx =
      parse_file folder ctx file
        (List.filter (fun x -> x <> "plth" && x <> "logic" && x <> file) deps)
    in
    (dones, ctx)

let rec parse_all folder dones_and_ctx = function
  | [] -> dones_and_ctx
  | file :: files ->
      parse_all folder (parse_module folder dones_and_ctx file) files

let main folder input_files =
  Printf.printf "Beginning the translation of %s.\n" folder;
  let _ = Api.Files.add_path folder in
  parse_all folder ([], Ast.empty_global_context) input_files

let folder = Sys.argv.(1)

let input_files =
  let list_files = Sys.readdir folder in
  List.filter (fun x -> Filename.extension x = ".dk") (Array.to_list list_files)

let _ = main folder (List.map Filename.remove_extension input_files)

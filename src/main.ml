module Files = Api.Files
module P = Parsers.Parser

(*
let rec parse_modules mds already_done = match mds with
  | [] -> already_done, []
  | md::rest -> 
    let deps = Deps.deps_of_md md in
    (* retirer already_done de deps *)
    begin match deps with
      | [] -> (md::already_done, parse md) 
      | _ -> parse_modules deps already_done 
             retirer deps de rest
             parse md
             parse_modules rest
    end
*)

let test1 file out ctx entry : Ast.global_context =
  let entry, context_entry = Parse.parse_entry file ctx entry in
  Printf.fprintf out "%s\n\n" (Coq.string_of_decl entry);
  context_entry :: ctx

let test file out ctx entry : Ast._global_context =
  let name, entry = New_parse.parse_entry file ctx entry in
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
  Printf.fprintf out "Require Import Coq.Logic.Classical_Prop.\n";
  Printf.fprintf out "\n"

let parse_file folder ctx file deps =
  let oc = open_out ("output/" ^ file ^ ".v") in
  Printf.printf "\nWe are parsing %s.\n%!" file;
  let entries = P.(parse (input_from_file (folder ^ file ^ ".dk"))) in
  print_deps oc deps;
  let ctx = List.fold_left (test file oc) ctx entries in
  Printf.printf "Finish with %s.\n\n%!" file;
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
  let dones, todo, ctx = dones_and_ctx in
  if List.mem file dones && not (List.mem file todo) then (dones, todo, ctx)
  else
    let env =
      Api.Env.init (Parsers.Parser.input_from_file (folder ^ file ^ ".dk"))
    in
    let md = Api.Env.get_name env in
    let _ =
      Printf.printf "We want to parse %s.\n" (Kernel.Basic.string_of_mident md)
    in
    let deps = dep_of_file folder file in
    let deps_files =
      List.filter
        (fun x ->
          x <> "plth" && x <> "logic" && x <> file && not (List.mem x dones))
        deps
    in
    List.iter (Printf.printf "%s  ") deps_files;
    Printf.printf "\n";
    let todo = List.append todo deps_files in
    let dones = file :: dones in
    let todo = List.filter (fun x -> x != file) todo in
    let dones, todo, ctx =
      List.fold_left (parse_module folder) (dones, todo, ctx) deps_files
    in
    let ctx =
      parse_file folder ctx file
        (List.filter (fun x -> x <> "plth" && x <> "logic" && x <> file) deps)
    in
    (dones, todo, ctx)

let rec parse_all folder dones_and_ctx = function
  | [] -> dones_and_ctx
  | file :: files ->
      parse_all folder (parse_module folder dones_and_ctx file) files
(*
let main input_file =
  let _ = Api.Files.add_path "input/" in
  let entries = P.(parse (input_from_file input_file)) in
  let env = Api.Env.init (Parsers.Parser.input_from_file input_file) in
  let _ = Printf.printf "%s\n" (Coq.string_of_coq_prop Coq.coq_string_test) in
  let _ = List.hd entries in
  let md = Api.Env.get_name env in 
  Printf.printf "\n\nThe main file is %s.\n\n" (Kernel.Basic.string_of_mident md);
  let deps = Deps.deps_of_md ~transitive:false md in
  let deps = Kernel.Basic.MidentSet.elements deps in
  let deps = List.map Kernel.Basic.string_of_mident deps in 
  let deps_files = List.map (fun s -> "input/" ^ s ^ ".dk") deps in
  let _ = List.map (fun file -> parse_file [] file) deps_files in
  let _ = parse_file [] (input_file) in
  List.iter (fun x -> Printf.printf "Require %s.\n\n" x) deps
*)

let main folder input_files =
  let _ = Printf.printf "\nBeginning.\n" in
  let _ = Api.Files.add_path folder in
  let _ = Api.Files.add_path "input" in
  let _ = test1 in
  (*parse_all folder ([], input_files, []) input_files *)
  parse_all folder ([], input_files, Ast.empty_global_context) input_files

let folder = Sys.argv.(1)

let input_files =
  let list_files = Sys.readdir folder in
  List.filter (fun x -> Filename.extension x = ".dk") (Array.to_list list_files)

let _ = main folder (List.map Filename.remove_extension input_files)

(*"input/euclid/lemma__equalityplth.eqsymmetric.dk" *)
(*"euclidean__axioms"*)

(*let deps = Deps.dep_of_entry [md; Kernel.Basic.mk_mident "plth"] x in *)

(* Have some tests
   Format.printf "%a OK" Api.Pp.Default.print_entry e;
*)

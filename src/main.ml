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



let parse_file ctx file =
  Printf.printf "\nWe are parsing %s.\n" file;
  let entries = P.(parse (input_from_file file)) in 
  let ctx = List.fold_left (Parse.parse_entry file) ctx entries in
  List.iter (fun x -> Printf.printf "%s\n" (Coq.string_of_decl x)) ctx;
  Printf.printf "Finish with %s.\n\n" file;
  ctx


let rec parse_module dones_and_ctx file =
  let (dones, ctx) = dones_and_ctx in
  let env = Api.Env.init (Parsers.Parser.input_from_file file) in
  let md = Api.Env.get_name env in 
  let _ =  Printf.printf "We want to parse %s.\n" (Kernel.Basic.string_of_mident md) in
  let deps = Deps.deps_of_md ~transitive:false md in
  let deps = Kernel.Basic.MidentSet.elements deps in
  let deps = List.map Kernel.Basic.string_of_mident deps in
  let deps_files = 
    List.filter (fun x -> x <> "input/euclid/plth.dk" && x <> "input/euclid/logic.dk" && x <> file && (not (List.mem x dones))) 
    (List.map (fun s -> "input/euclid/" ^ s ^ ".dk") deps) in
  let dones = List.append dones deps_files in
  let (dones, ctx) = List.fold_left parse_module (dones, ctx) deps_files in
  let ctx = parse_file ctx file in
  (dones, ctx)


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

let main input_file = 
  let _ = Printf.printf "\nBeginning.\n" in
  let _ = Api.Files.add_path "input/euclid" in
  let _ = Api.Files.add_path "input" in
  parse_module ([], []) input_file

let _ = main "input/euclid/lemma__equalitysymmetric.dk"




  (*let deps = Deps.dep_of_entry [md; Kernel.Basic.mk_mident "plth"] x in *)

(* Have some tests
Format.printf "%a OK" Api.Pp.Default.print_entry e;
*)
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



let parse_module ctx m =
  Printf.printf "\n\nThe module is %s.\n\n" m;
  let entries = P.(parse (input_from_file m)) in 
  let l = List.map (Parse.parse_entry ctx) entries in
  (m, l)
  (* List.iter (fun x -> Printf.printf "%s\n" (Coq.string_of_decl x)) l *)


let main input_file =
  let _ = Api.Files.add_path "input/" in
  let entries = P.(parse (input_from_file input_file)) in
  let env = Api.Env.init (Parsers.Parser.input_from_file input_file) in
  let _ = Printf.printf "%s\n" (Coq.string_of_coq_prop Coq.coq_string_test) in
  let _ = List.hd entries in
  let md = Api.Env.get_name env in 
  Printf.printf "\n\nThe module is %s.\n\n" (Kernel.Basic.string_of_mident md);
  (*let deps = Deps.dep_of_entry [md; Kernel.Basic.mk_mident "plth"] x in *)
  let deps = Deps.deps_of_md ~transitive:true md in
  let deps = Kernel.Basic.MidentSet.elements deps in
  let deps = List.map Kernel.Basic.string_of_mident deps in 
  let deps_files = List.map (fun s -> "input/" ^ s ^ ".dk") deps in
  let _ = List.map (fun file -> parse_module [] file) deps_files in
  let _ = parse_module [] (input_file) in
  List.iter (fun x -> Printf.printf "Require %s.\n\n" x) deps


let _ = main "input/test.dk"


(* Have some tests
Format.printf "%a OK" Api.Pp.Default.print_entry e;
*)
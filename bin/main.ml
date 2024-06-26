open Viper
open Gospel
(* open Tmodule *)
open Format

let fname = ref None
let version = "0.1~dev"

let spec =
  [
    ( "--version",
      Arg.Unit
        (fun () ->
          printf "gospel2viper %s@." version;
          exit 0),
      " print version information" );
  ]

let usage_msg = sprintf "%s <file>.ml\nVerify OCaml program\n" Sys.argv.(0)

let usage () =
  Arg.usage spec usage_msg;
  exit 1

let set_file f =
  match !fname with
  | None when Filename.check_suffix f ".ml" -> fname := Some f
  | _ -> usage ()

let () = Arg.parse spec set_file usage_msg
let fname = match !fname with None -> usage () | Some f -> f

(* let path2module p =
  Filename.basename p |> Filename.chop_extension |> String.capitalize_ascii *)

let base_fname f = Filename.basename f |> Filename.chop_extension

(* let type_check load_path name sigs =
  let md = init_muc name in
  let mn = path2module name in
  let penv =
     Utils.Sstr.singleton mn |> Typing.penv load_path
  in
  let md = List.fold_left (Typing.type_sig_item penv) md sigs in
  wrap_up_muc md *)

let () =
  let open Parser_frontend in
    (* let load_path = [ Filename.dirname fname ] in *)
  let ic = open_in fname in
  let lb = Lexing.from_channel ic in
  Location.init lb fname;
  let ocaml_structure = parse_ocaml_structure_lb lb in
  let ocaml = Uattr2spec.structure ~filename:fname ocaml_structure in
  let file_viper = Gospel2viper.cameleer_structure ocaml in
  let out_fname = base_fname fname ^ "_ml.vpr" in
  let base_dir =
    "/home/cha/Documents/github/gospel2viper/example/translation_ml_"
    ^ (String.capitalize_ascii (base_fname fname)) in
  let () = if not (Sys.file_exists base_dir) then
    Sys.mkdir base_dir 0o755 else () in
  let directory = base_dir ^ "/" ^ out_fname in

  let fmt = formatter_of_out_channel (open_out directory) in
  fprintf fmt "%s@." (Print_viper.print file_viper)


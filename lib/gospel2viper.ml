open Gospel
open Viper_ast

let rec flat_list l =
  match l with
  | [] -> []
  | hd :: tl -> hd @ flat_list tl

let pp_hashtbl ty_ht = Hashtbl.iter (fun x y ->
  Printf.printf "%s -> \n" x; Format.printf "";
  List.iter (fun (m, t)-> Format.printf " [%s: %s] " m t) y;
  Format.printf "@.") ty_ht

let to_type t =
  match t.Parsetree.ptyp_desc with
  | Ptyp_constr (lident, []) ->
    (match lident.txt with
    | Lident s -> TyApp (s, [])
    | _ -> assert false)
  | Ptyp_constr (_lident, _l) -> assert false
    (*
    | Ptyp_any  (** [_] *)
    | Ptyp_var of string  (** A type variable such as ['a] *)
    | Ptyp_arrow of arg_label * core_type * core_type
    | Ptyp_tuple of core_type list
    | Ptyp_object of object_field list * closed_flag
    | Ptyp_class of Longident.t loc * core_type list
    | Ptyp_alias of core_type * string  (** [T as 'a]. *)
    | Ptyp_variant of row_field list * closed_flag * label list option
    | Ptyp_poly of string loc list * core_type
    | Ptyp_package of package_type  (** [(module S)]. *)
    | Ptyp_extension of extension  (** [[%id]]. *)
    *)
    | _ -> assert false

let rec to_field (lbls: Parsetree.label_declaration list) : decl list =
  match lbls with
  | [] -> []
  | lbl :: tl ->
    DField (lbl.pld_name.txt, to_type lbl.pld_type) :: to_field tl

let to_type_def decl =
  match decl.Uast.tkind with
  | Ptype_record lbls -> to_field lbls
  (*
  | Ptype_abstract
  | Ptype_variant of constructor_declaration list
  | Ptype_record of label_declaration list
  | Ptype_open
  *)
  | _ -> assert false

let tmp_known_types = function
  | "int" -> true
  | _ -> false


let get_ty_lbl pty =
  match pty with
  | Uast.PTtyapp (Qpreid preid, []) -> preid.pid_str
  | Uast.PTtyapp (_qualid, _l) -> assert false
  (*
  | PTtyvar of Preid.t
  | PTtuple of pty list
  | PTarrow of labelled_arg * pty * pty
  *)
  | _ -> assert false

let rec to_args ty_ht fl =
  match fl with
  | [] -> []
  | (_loc, preid, pty) :: tl ->
    let str = get_ty_lbl pty in
    (match Hashtbl.find_opt ty_ht str with
      | None -> (preid.Identifier.Preid.pid_str, TyApp (str, [])) :: to_args ty_ht tl
      | Some l ->
        let rec add_models (l: (string * string) list) = match l with
          | [] -> []
          | (m, t) :: tl -> (m, TyApp (t, [])) :: add_models tl
        in
        ((preid.Identifier.Preid.pid_str, TyApp ("Ref", [])) :: (add_models l)) @ to_args ty_ht tl)

let rec get_spec_fields (spec: Gospel.Uast.field list) =
  match spec with
  | [] -> []
  | hd :: tl ->
    (hd.Uast.f_preid.pid_str, get_ty_lbl hd.Uast.f_pty) :: get_spec_fields tl

let struct_desc ty_ht d =
  match d with
  | Uast.Str_type (_recf, ty_decl :: _ands) ->
    (* For the moment, no "and" in type declaration *)
    let model_typed_list = (
      match ty_decl.tspec with
      | None -> []
      | Some spec -> get_spec_fields spec.ty_field) in
    Hashtbl.add ty_ht ty_decl.tname.txt model_typed_list;
    to_type_def ty_decl
  | Str_function f ->
    [DPredicate {
      pred_name = f.fun_name.pid_str;
      pred_body = None;
      pred_args = to_args ty_ht f.fun_params;
    }]
  (*
  | Str_eval of s_expression * attributes
  | Str_value of rec_flag * s_value_binding list
  | Str_primitive of s_val_description
  | Str_typext of type_extension
  | Str_exception of type_exception
  | Str_module of s_module_binding
  | Str_recmodule of s_module_binding list
  | Str_modtype of s_module_type_declaration
  | Str_open of open_declaration
  | Str_class of class_declaration list
  | Str_class_type of class_type_declaration list
  | Str_include of include_declaration
  | Str_attribute of attribute
  | Str_extension of extension * attributes
  | Str_function of function_
  | Str_prop of prop
  | Str_ghost_type of rec_flag * s_type_declaration list
  | Str_ghost_val of s_val_description
  | Str_ghost_open of open_declaration
  *)
  | _ -> assert false


let cameleer_structure_item ty_ht i = struct_desc ty_ht i.Uast.sstr_desc

let cameleer_structure (s: Uast.s_structure) =
  let ty_ht = Hashtbl.create 8 in
  flat_list (List.map (fun item -> cameleer_structure_item ty_ht item) s)

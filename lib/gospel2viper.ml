open Gospel
open Viper_ast

type type_storage = {
  mutable fields: string list;
  mutable models: (string * ty) list;
  mutable null_field: string option; }

(* printers for debuging *)
let rec pp_ty ty =
  match ty with
  | TyApp (s, tys) -> Format.printf "%s" s;
    if tys <> [] then Format.printf "["; List.iter (fun e -> pp_ty e) tys; Format.printf "]"
  | TyVar s -> Format.printf "%s" s

let pp_hashtbl ty_ht = Hashtbl.iter (fun x (y: type_storage) ->
  Printf.printf "%s -> \n" x; Format.printf "\tfields:: ";
  List.iter (fun field -> Format.printf "%s " field) y.fields;
  Format.printf "\n\tmodels::";
  List.iter (fun (m, ty)-> Format.printf "(%s: " m; pp_ty ty; Format.printf ")") y.models;
  Format.printf "\n\tnull_field:: %s" (match y.null_field with None -> "None" | Some s -> "Some " ^ s);
  Format.printf "@.") ty_ht

let ty_ht = Hashtbl.create 8

let keyword = function
  | "int"  -> "Int"
  | "bool" -> "Bool"
  | "sequence" -> "Seq"
  | "infix +"  -> "+"
  | "infix -"  -> "-"
  | "infix *"  -> "*"
  | "infix /"  -> "/"
  | "infix >"  -> ">"
  | "infix >=" -> ">="
  | "infix <"  -> "<"
  | "infix <=" -> "<="
  | "infix ="  -> "=="
  | "infix <>" -> "!="
  | "infix ++" -> "++"
  | default -> default

let to_type t =
  match t.Parsetree.ptyp_desc with
  | Ptyp_constr (lident, []) ->
    (match lident.txt with
    | Lident s -> if Hashtbl.mem ty_ht s
      then TyApp("Ref", [])
      else TyApp (keyword s, [])
    | _ -> assert false)
  | Ptyp_constr _ -> assert false
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

let rec to_field lbls =
  match lbls with
  | [] -> [], []
  | lbl :: tl ->
    let sl, decls = to_field tl in
    lbl.Parsetree.pld_name.txt :: sl,
    DField (lbl.pld_name.txt, to_type lbl.pld_type) :: decls

let rec to_fields constrdecls =
  match constrdecls with
  | [] -> [], []
  | constrdecl :: tl ->
    let (stringl, decll) = (match constrdecl.Parsetree.pcd_args with
    | Pcstr_tuple [] -> ([], [])
    | Pcstr_record lbls -> to_field lbls
    | _ -> assert false
    ) in
    let sl, decls = to_fields tl in stringl @ sl, decll @ decls

let get_payload_name payload =
  match payload with
  | Parsetree.PStr [{pstr_desc; _}] ->
    (match pstr_desc with
    | Pstr_eval (exp, _) ->
      (match exp.pexp_desc with
      | Pexp_constant s ->
        (match s with
        | Pconst_string (s, _, _) -> s
        | _ -> assert false)
      | _ -> assert false)
    (*
    | Pstr_value of rec_flag * value_binding list
        (** [Pstr_value(rec, [(P1, E1 ; ... ; (Pn, En))])] represents:
              - [let P1 = E1 and ... and Pn = EN]
                  when [rec] is {{!Asttypes.rec_flag.Nonrecursive}[Nonrecursive]},
              - [let rec P1 = E1 and ... and Pn = EN ]
                  when [rec] is {{!Asttypes.rec_flag.Recursive}[Recursive]}.
          *)
    | Pstr_primitive of value_description
        (** - [val x: T]
              - [external x: T = "s1" ... "sn" ]*)
    | Pstr_type of rec_flag * type_declaration list
        (** [type t1 = ... and ... and tn = ...] *)
    | Pstr_typext of type_extension  (** [type t1 += ...] *)
    | Pstr_exception of type_exception
        (** - [exception C of T]
              - [exception C = M.X] *)
    | Pstr_module of module_binding  (** [module X = ME] *)
    | Pstr_recmodule of module_binding list
        (** [module rec X1 = ME1 and ... and Xn = MEn] *)
    | Pstr_modtype of module_type_declaration  (** [module type S = MT] *)
    | Pstr_open of open_declaration  (** [open X] *)
    | Pstr_class of class_declaration list
        (** [class c1 = ... and ... and cn = ...] *)
    | Pstr_class_type of class_type_declaration list
        (** [class type ct1 = ... and ... and ctn = ...] *)
    | Pstr_include of include_declaration  (** [include ME] *)
    | Pstr_attribute of attribute  (** [[\@\@\@id]] *)
    | Pstr_extension of extension * attributes  (** [[%%id]] *)
    *)
    | _ -> assert false)
  (*
  | PSig of signature  (** [: SIG] in an attribute or an extension point *)
  | PTyp of core_type  (** [: T] in an attribute or an extension point *)
  | PPat of pattern * expression option
  *)
  | _ -> assert false

let rec get_attributes attrs =
  match attrs with
  | [] -> []
  | attr :: tl ->
    (attr.Parsetree.attr_name.txt, get_payload_name attr.attr_payload )
    :: get_attributes tl

let find_attr attrs target_name target_field =
  List.exists (fun (name, field) ->
    name = target_name && field = target_field) attrs

let to_type_def decl =
  match decl.Uast.tkind with
  | Ptype_record lbls ->
    to_field lbls, None
  | Ptype_variant constr_l ->
    (match constr_l with
    | constr :: _tl ->
      let attrs = get_attributes constr.pcd_attributes in
      let str_opt = if find_attr attrs "viper" "null"
        then Some (constr.pcd_name.txt)
        else None in
      to_fields constr_l, str_opt
    | _ -> assert false)
  (*
  | Ptype_abstract
  | Ptype_open
  *)
  | _ -> assert false

let rec to_string = function
  | Uast.Qpreid s -> s.pid_str
  | Qdot (qualid, s) -> to_string qualid ^ "." ^ s.pid_str

let rec get_ty_lbl pty =
  match pty with
  | Uast.PTtyapp (Qpreid preid, []) -> keyword preid.pid_str
  | Uast.PTtyapp (_name, hd :: _tl) -> get_ty_lbl hd
  (*
  | PTtyvar of Preid.t
  | PTtuple of pty list
  | PTarrow of labelled_arg * pty * pty
  *)
  | _ -> assert false

let rec to_ty ty =
  match ty with
  | Uast.PTtyapp (name, tys) ->
    TyApp (keyword (to_string name), to_ty_list tys)
  | _ -> assert false
and to_ty_list = function
  | [] -> []
  | t :: tl -> to_ty t :: to_ty_list tl

let rec to_args fl =
  match fl with
  | [] -> []
  | (_loc, preid, pty) :: tl ->
    let ty = to_ty pty in
    let str = get_ty_lbl pty in
    (if Hashtbl.mem ty_ht str
    then (preid.Identifier.Preid.pid_str, TyApp ("Ref", []))
    else (preid.Identifier.Preid.pid_str, ty) ) :: to_args tl

let rec get_spec_fields spec =
  match spec with
  | [] -> []
  | hd :: tl ->
    (hd.Uast.f_preid.pid_str, to_ty hd.Uast.f_pty) :: get_spec_fields tl

let to_const = function
  | Parsetree.Pconst_integer (n, _char_opt) -> TConst (int_of_string n)
  (*
  | Pconst_char of char
  | Pconst_string of label * location * label option
  | Pconst_float of label * char option
  *)
  | _ -> assert false

let to_binop = function
  | Uast.Tand | Tand_asym -> BAnd
  | Tor | Tor_asym -> BOr
  | Timplies -> BImpl
  | Tiff -> assert false

let is_field_null ty_ht str_field =
  Hashtbl.fold (fun _ y acc -> acc ||
  match y.null_field with None -> false | Some s -> s = str_field) ty_ht false

let rec to_term term =
  match term.Gospel.Uast.term_desc with
  | Ttrue  -> TBool true
  | Tfalse -> TBool false
  | Tconst c -> to_const c
  | Tbinop (t1, binop, t2) ->
    TBinop (to_term t1, to_binop binop, to_term t2)
  | Tinfix (t1, infix, t2) ->
    TInfix (to_term t1, keyword infix.pid_str, to_term t2)
  | Tpreid name ->
    (match to_string name with
    | "empty" | "Sequence.empty" -> TSeq (TEmpty (TyVar "Int"))
    | null_field when is_field_null ty_ht null_field -> TNull
    | default -> TVar (None, default))
  | Tfield (term, field) ->
    TVar (Some (to_term term), to_string field)
  | Tapply (hd, term) ->
    let argv = to_fun hd @ to_fun term in
    let args = List.tl argv in
    let fun_name = (match List.hd argv with
    | TVar (_, s) -> s
    | _ -> assert false) in
    (match fun_name with
    | "get" | "Sequence.get" -> (match args with
      | [n; num] -> TSeq (TGet (n, num))
      | _ -> assert false)
    | "length" | "Sequence.length" -> TSeq (TLength (List.hd args))
    | "tl" | "Sequence.tl"     -> TSeq (TSub (List.hd args, (TConst 1), None))
    | "hd" | "Sequence.hd"     -> TSeq (TGet (List.hd args, (TConst 0)))
    | "singleton" | "Sequence.singleton" -> TSeq (TSingleton (List.hd args))
    | default  -> TApp (None, default, args))
  | Tlet (name, t1, t2) ->
    TLet (name.pid_str, to_term t1, to_term t2)
  | Tif (tif, tthen, telse) ->
    TTernary (to_term tif, to_term tthen, to_term telse)
  | Tidapp (name, terms) ->
    let str = to_string name in
    if String.starts_with ~prefix:"mixfix" str then
      (match str, terms with
      | "mixfix [_]",    [name; t2] ->
        TSeq (TGet (to_term name, to_term t2))
      | "mixfix [_.._]", [name; min; max] ->
        TSeq (TSub (to_term name, to_term min, Some(to_term max)))
      | "mixfix [.._]",  [name; max] ->
        TSeq (TSub (to_term name, TConst 0, Some(to_term max)))
      | "mixfix [_..]",  [name; min] ->
        TSeq (TSub (to_term name, to_term min, None))
      | _ -> assert false)
    else (match terms with
    | [t1; t2] ->
      TInfix (to_term t1, keyword (to_string name), to_term t2)
    | _ -> assert false)
  (*
  | Tidapp of qualid * term list
  | Tnot of term
  | Tquant of quant * binder list * term
  | Tattr of string * term
  | Tcase of term * (pattern * term) list
  | Tcast of term * pty
  | Ttuple of term list
  | Trecord of (qualid * term) list
  | Tupdate of term * (qualid * term) list
  | Tscope of qualid * term
  | Told of term
  *)
  | Tpoints (Qpreid id, fields) ->
    let mk_acc (field, _) = match field with
      | Uast.Qdot _ -> assert false (* TODO *)
      | Qpreid field ->
        Identifier.Preid.(TAcc (id.pid_str, field.pid_str)) in
    let mk_and = function
      | [] -> assert false
      | field :: xs ->
        List.fold_left (fun acc f -> TBinop (acc, BAnd, f)) field xs in
    let fields_acc = List.rev (List.map mk_acc fields) in
    mk_and fields_acc
  | Tpoints (Qdot _, _) ->
      assert false (* TODO *)
  | Tnot _ -> assert false (* TODO *)
  | Tquant _ -> assert false (* TODO *)
  | _ -> assert false (* TODO *)
(* and to_term_list t = *)
(*   match t with *)
(*   | Gospel.Uast.Ttuple terms -> (match terms with *)
(*     | [] -> [] *)
(*     | hd :: tl -> to_term hd :: to_term_list (Ttuple tl)) *)
(*   | _ -> assert false *)

and to_fun t : term list =
  (match t.Gospel.Uast.term_desc with
  | Gospel.Uast.Tpreid _ -> [to_term t]
  | Tapply (hd2, t2) -> to_fun hd2 @ to_fun t2
  | _ -> [to_term t])

let to_def term_opt =
  match term_opt with
  | None -> None
  | Some term -> Some (to_term term)

let to_fun_body term_opt : term option =
  match term_opt with
  | None -> None
  | Some term -> Some (to_term term)

let rec scan_args fl =
  match fl with
  | [] -> []
  | (_loc, preid, pty) :: tl ->
    (match Hashtbl.find_opt ty_ht (get_ty_lbl pty) with
    | None   -> []
    | Some l ->
      let rec iter = function
      | [] -> []
      | n :: tl -> (preid.Identifier.Preid.pid_str, n) :: iter tl in
      iter l.fields) @ scan_args tl

let to_spec (spec_opt : Gospel.Uast.fun_spec option): spec =
  match spec_opt with
  | None -> {spec_pre = []; spec_post = [];}
  | Some spec ->
    {spec_pre = List.map to_term spec.fun_req;
    spec_post = List.map to_term spec.fun_ens}
let struct_desc d =
  match d with
  | Uast.Str_type (_recf, ty_decl :: _ands) ->
    (* For the moment, no "and" in type declaration *)
    let models = (match ty_decl.tspec with
    | None -> []
    | Some spec -> get_spec_fields spec.ty_field) in
    Hashtbl.add ty_ht ty_decl.tname.txt
      {fields = []; models = []; null_field = None};
    let (fields, r), null_field = to_type_def ty_decl in
    Hashtbl.replace ty_ht ty_decl.tname.txt {fields; models; null_field}; r
  | Str_function f ->
    let args = to_args f.fun_params in
    (match f.fun_type with
    | None ->
      [DPredicate {
        pred_name = f.fun_name.pid_str;
        pred_body = to_def f.fun_def;
        pred_args = args;
      }]
    | Some ret_ty -> [DFunction {
        function_name = f.fun_name.pid_str;
        function_args = args;
        function_rety = to_ty ret_ty;
        function_spec = to_spec f.fun_spec;
        function_body = to_fun_body f.fun_def;
    }])
    | Str_value (_rec_f, _bindings) -> assert false
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
  | Str_prop of prop
  | Str_ghost_type of rec_flag * s_type_declaration list
  | Str_ghost_val of s_val_description
  | Str_ghost_open of open_declaration
  *)
  | _ -> assert false

let cameleer_structure_item i = struct_desc i.Uast.sstr_desc

let cameleer_structure (s: Uast.s_structure) =
  List.flatten (List.map (fun item -> cameleer_structure_item item) s)

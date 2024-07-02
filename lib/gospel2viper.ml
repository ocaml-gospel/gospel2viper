open Gospel
open Viper_ast

type type_storage =
  {mutable fields: string list; mutable models: (string * ty) list}

let ty_ht = Hashtbl.create 8

let rec flat_list l =
  match l with
  | [] -> []
  | hd :: tl -> hd @ flat_list tl

let keyword = function
  | "int" -> "Int"
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
  | default -> default

let to_type t =
  match t.Parsetree.ptyp_desc with
  | Ptyp_constr (lident, []) ->
    (match lident.txt with
    | Lident s ->
      if Hashtbl.mem ty_ht s then TyApp("Ref", [])
      else TyApp (keyword s, [])
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

let rec to_field lbls =
  match lbls with
  | [] -> [], []
  | lbl :: tl ->
    let sl, decls = to_field tl in
    lbl.Parsetree.pld_name.txt :: sl,
    DField (lbl.pld_name.txt, to_type lbl.pld_type) :: decls

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

let qualid_to_string = function
  | Uast.Qpreid s -> s.pid_str
  | Qdot _ -> assert false

let rec get_ty_lbl pty =
  match pty with
  | Uast.PTtyapp (Qpreid preid, []) -> keyword preid.pid_str
  | Uast.PTtyapp (_qualid, hd :: _tl) -> get_ty_lbl hd
  (*
  | PTtyvar of Preid.t
  | PTtuple of pty list
  | PTarrow of labelled_arg * pty * pty
  *)
  | _ -> assert false

let rec to_ty (ty: Uast.pty) : ty =
  match ty with
  | PTtyapp (qualid, tys) ->
    TyApp (keyword (qualid_to_string qualid), to_ty_list tys)
  | _ -> assert false
and to_ty_list =
  function
    | [] -> []
    | t :: tl -> to_ty t :: to_ty_list tl

let rec to_args fl =
  match fl with
  | [] -> []
  | (_loc, preid, pty) :: tl ->
    let ty = to_ty pty in
    let str = get_ty_lbl pty in
    if Hashtbl.mem ty_ht str
    then (preid.Identifier.Preid.pid_str, TyApp ("Ref", [])) :: to_args tl
    else (preid.Identifier.Preid.pid_str, ty) :: to_args tl

let rec get_spec_fields (spec: Gospel.Uast.field list) : (string * ty) list =
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

let rec to_term (arg_names : string list) = function
  | Gospel.Uast.Ttrue -> TBool true
  | Tfalse -> TBool false
  | Tconst c -> to_const c
  | Tbinop (t1, binop, t2) -> TBinop
    (to_term arg_names t1.term_desc,
    to_binop binop,
    to_term arg_names t2.term_desc)
  | Tinfix (t1, infix, t2) -> TInfix
    (to_term arg_names t1.term_desc,
    keyword infix.pid_str,
    to_term arg_names t2.term_desc)
  | Tpreid x -> TVar (None, qualid_to_string x)
  | Tfield (term, qualid) ->
    let arg = qualid_to_string qualid in
    TVar ((if List.mem arg arg_names then None else
      Some (to_term arg_names term.term_desc)), arg)
  | Tapply (hd, term) ->
    let argv = to_fun arg_names hd @ to_fun arg_names term in
    let args = List.tl argv in
    let fun_name =
      (match List.hd argv with
      | TVar (_, s) -> s
      | _ -> assert false) in
    (match fun_name with
      | "length" -> TSeq (TLength (List.hd args))
      | "get"    ->
        (match args with
        | [n; num] -> TSeq (TGet (n, num))
        | _ -> assert false)
      | "tl"     -> TSeq(TSub (List.hd args, (TConst 1), None))
      | "hd"     -> TSeq(TGet (List.hd args, (TConst 0)))
      | default -> TApp(None, default, args))
  | Tlet (name, t1, t2) ->
    TLet (name.pid_str, to_term arg_names t1.term_desc, to_term arg_names t2.term_desc)
  (*
  | Tidapp of qualid * term list
  | Tnot of term
  | Tif of term * term * term
  | Tquant of quant * binder list * term
  | Tattr of string * term
  | Tlet of Preid.t * term * term
  | Tcase of term * (pattern * term) list
  | Tcast of term * pty
  | Ttuple of term list
  | Trecord of (qualid * term) list
  | Tupdate of term * (qualid * term) list
  | Tscope of qualid * term
  | Told of term
  *)
  | _ -> assert false
and to_term_list arg_names t =
  match t with
  | Gospel.Uast.Ttuple terms ->
    (match terms with
    | [] -> []
    | hd :: tl -> to_term arg_names hd.term_desc :: to_term_list arg_names (Ttuple tl))
  | _ -> assert false
and to_fun arg_names t : term list =
  (match t.Gospel.Uast.term_desc with
  | Gospel.Uast.Tpreid _ as tpreid -> [to_term arg_names tpreid]
  | Tapply (hd2, t2) -> to_fun arg_names hd2 @ to_fun arg_names t2
  | _ -> [to_term arg_names t.term_desc])

let to_def fields_to_acc arg_names term_opt =
  match term_opt with
  | None -> None
  | Some term ->
    let rec iter = function
    | [] -> assert false
    | [(type_name, field)] -> TAcc (type_name, field)
    | (type_name, field) :: tl -> TBinop
      (TAcc(type_name, field), BAnd, iter tl) in
      Some (TBinop
      (iter fields_to_acc,
      BAnd,
      to_term arg_names term.Gospel.Uast.term_desc))

let rec scan_args fl =
  match fl with
  | [] -> []
  | (_loc, preid, pty) :: tl ->
    let ty_str = get_ty_lbl pty in
    (match Hashtbl.find_opt ty_ht ty_str with
    | None   -> []
    | Some l ->
      let rec iter = function
      | [] -> []
      | n :: tl -> (preid.Identifier.Preid.pid_str, n) :: iter tl in
      iter l.fields) @ scan_args tl

let struct_desc d =
  match d with
  | Uast.Str_type (_recf, ty_decl :: _ands) ->
    (* For the moment, no "and" in type declaration *)
    let models = (match ty_decl.tspec with
    | None -> []
    | Some spec -> get_spec_fields spec.ty_field) in
    Hashtbl.add ty_ht ty_decl.tname.txt {fields = []; models = []};
    let fields, r = to_type_def ty_decl in
    Hashtbl.replace ty_ht ty_decl.tname.txt {fields; models}; r
  | Str_function f ->
    let args = to_args f.fun_params in
    let arg_names = List.map (fun (n, _t) -> n) args in
    let fields_to_acc = scan_args f.fun_params in
    [DPredicate {
      pred_name = f.fun_name.pid_str;
      pred_body = to_def fields_to_acc arg_names f.fun_def;
      pred_args = args;
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

let cameleer_structure_item i = struct_desc i.Uast.sstr_desc

let cameleer_structure (s: Uast.s_structure) =
  flat_list (List.map (fun item -> cameleer_structure_item item) s)

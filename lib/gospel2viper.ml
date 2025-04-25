open Gospel
open Viper_ast

(* printers for debuging *)
let rec pp_ty ty =
  match ty with
  | TyApp (s, tys) -> Format.printf "%s" s;
    if tys <> [] then Format.printf "[";
    List.iter (fun e -> pp_ty e) tys; Format.printf "]"
  | TyVar s -> Format.printf "%s" s
  | TyEmpty -> Format.printf "EMPTY TYPE"

type args = {
  name: string;
  ty: string;
}

type constructor = string * args list

type adt = constructor list

let adts : (string, adt) Hashtbl.t = Hashtbl.create 8

let pp_adt adt = List.iter (fun (constructor, args) ->
  Format.printf "%s : " constructor;
  List.iter (fun arg -> Format.printf "{name: %s\tty: %s}@." arg.name arg.ty) args
  ) adt

let pp_adts adts = Hashtbl.iter (fun k v -> Format.printf "%s ->\n" k; pp_adt v) adts

let types = ref ["Int"]

let cons_name = "X"

let is_infix str =
  List.mem str ["+"; "-"; "*"; "/"; ">"; ">="; "<"; "<="; "=="; "!="]

let keyword = function
  | "int"  -> "Int"
  | "bool" -> "Bool"
  | "sequence" -> "Seq"
  | "infix ++" -> "++"
  | "infix +"  -> "+"
  | "infix -"  -> "-"
  | "infix *"  -> "*"
  | "infix /"  -> "/"
  | "infix >"  -> ">"
  | "infix >=" -> ">="
  | "infix <"  -> "<"
  | "infix <=" -> "<+"
  | "="  | "infix ="  -> "=="
  | "<>" | "infix <>" -> "!="
  | default -> default

let core_type_to_ty t =
  match t.Parsetree.ptyp_desc with
  | Ptyp_constr (id, []) ->
    (match id.txt with
    | Lident s -> TyApp (keyword s, [])
    | _ -> assert false)
  | Ptyp_constr _ -> assert false
  (*
  | Ptyp_any
  | Ptyp_var of string
  | Ptyp_arrow of arg_label * core_type * core_type
  | Ptyp_tuple of core_type list
  | Ptyp_object of object_field list * closed_flag
  | Ptyp_class of Longident.t loc * core_type list
  | Ptyp_alias of core_type * string
  | Ptyp_variant of row_field list * closed_flag * label list option
  | Ptyp_poly of string loc list * core_type
  | Ptyp_package of package_type
  | Ptyp_extension of extension
  *)
  | _ -> assert false (* TODO *)

let rec lbls_to_field = function
  | [] -> []
  | lbl :: tl ->
    let decls = lbls_to_field tl in
    DField (lbl.Parsetree.pld_name.txt, core_type_to_ty lbl.pld_type) :: decls

let get_payload_lbl = function
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
    | Pstr_primitive of value_description
    | Pstr_type of rec_flag * type_declaration list
    | Pstr_typext of type_extension
    | Pstr_exception of type_exception
    | Pstr_module of module_binding
    | Pstr_recmodule of module_binding list
    | Pstr_modtype of module_type_declaration
    | Pstr_open of open_declaration
    | Pstr_class of class_declaration list
    | Pstr_class_type of class_type_declaration list
    | Pstr_include of include_declaration
    | Pstr_attribute of attribute
    | Pstr_extension of extension * attributes
    *)
    | _ -> assert false) (* TODO *)
  (*
  | PSig of signature
  | PTyp of core_type
  | PPat of pattern * expression option
  *)
  | _ -> assert false (* TODO *)

let rec id_to_string = function
  | Uast.Qpreid s -> s.pid_str
  | Qdot (qualid, s) -> id_to_string qualid ^ "." ^ s.pid_str

let rec term_to_expr term =
  match term.Gospel.Uast.term_desc with
  | Ttrue -> EBool true
  | Tpreid id ->
    (match id_to_string id with
    | "[]" | "empty" | "Sequence.empty" -> ESeq (EEmpty (TyVar "Int"))
    | "Nil" -> ENull
    | default -> EVariable default)
  | Tfield (term, qualid) -> EField (term_to_expr term, id_to_string qualid)
  | Tapply (_hd, _t) ->
    let rec aux e = match e.Gospel.Uast.term_desc with
    | Tapply (t1, t2) -> (aux t1) @ [t2]
    | _ -> [e] in
    let tl = aux term in
    let fun_name = (match (List.hd tl).term_desc with
    | Tpreid s -> id_to_string s
    | _ -> assert false) in
    let args = List.tl (to_term_list tl) in
    (match fun_name with
    | "get" | "Sequence.get" ->
      (match args with
      | [n; num] -> ESeq (EGet (n, num))
      | _ -> assert false)
    | "length" | "Sequence.length" -> ESeq (ELength (List.hd args))
    | "tl" | "Sequence.tl"     ->
      ESeq (ESub (List.hd args, (EConst (CInt 1)), None))
    | "hd" | "Sequence.hd"     ->
      ESeq (EGet (List.hd args, (EConst (CInt 0))))
    | "singleton" | "Sequence.singleton" -> ESeq (ESingleton (List.hd args))
    | "cons" | "Sequence.cons" ->
      (match args with
      | [x; seq] -> ESeq (EConcat (ESeq (ESingleton x), seq))
      | _ -> assert false)
    | default  -> EApp (default, args))
  | Tidapp (id, es) ->
    let str = id_to_string id in
    if String.starts_with ~prefix:"mixfix" str then
      (match str, es with
      | "mixfix [_]",    [name; e2] ->
        ESeq (EGet (term_to_expr name, term_to_expr e2))
      | "mixfix [_.._]", [name; min; max] ->
        ESeq (ESub
        (term_to_expr name, term_to_expr min, Some(term_to_expr max)))
      | "mixfix [.._]",  [name; max] ->
        ESeq (ESub
        (term_to_expr name, EConst (CInt 0), Some(term_to_expr max)))
      | "mixfix [_..]",  [name; min] ->
        ESeq (ESub (term_to_expr name, term_to_expr min, None))
      | _ -> assert false)
    else (match es with
    | [e1; e2] ->
      EInfix (term_to_expr e1, keyword (id_to_string id), term_to_expr e2)
    | _ -> assert false)
  | Tconst c -> (match c with
    | Pconst_integer (s, _) -> EConst (CInt (int_of_string s))
    | _ -> assert false)
  | _ -> assert false
and to_term_list tl =
  match tl with
  | [] -> []
  | hd :: tl -> term_to_expr hd :: to_term_list tl

let rec get_attributes = function
  | [] -> []
  | attr :: tl ->
    (attr.Parsetree.attr_name.txt, get_payload_lbl attr.attr_payload)
    :: get_attributes tl

let find_attribute attrs target_name target_field =
  List.exists (fun (name, field) ->
    name = target_name && field = target_field) attrs

let construct_adt variant tname =
  let adt : adt ref = ref [] in
  let fields, adt_cont =
    List.fold_left
      (fun (fields, acc) e ->
         let name = e.Parsetree.pcd_name.txt in
         match e.Parsetree.pcd_args with
         | Pcstr_tuple _l ->
            adt := (name, []) :: !adt;
          (fields, (name, None) :: acc)
         | Pcstr_record lbls ->
           let new_fields = lbls_to_field lbls in
           adt := (name, [{name = cons_name; ty = "Ref";}]) :: !adt;
           (new_fields, (name, Some(cons_name, TyVar("Ref"))) :: acc)
      )
      ([], [])
      variant
  in
  Hashtbl.add adts tname !adt;
  types := tname :: !types;
  List.rev adt_cont, fields

let to_type_def decl =
  match decl.Uast.tkind with
  | Ptype_record lbls ->
    lbls_to_field lbls
  | Ptype_variant constr_l ->
    let tname = decl.Uast.tname.txt in
    let adt_cont, decl_list = construct_adt constr_l tname in
    DAdt (tname, adt_cont) :: decl_list
  (*
  | Ptype_abstract
  | Ptype_open
  *)
  | _ -> assert false (* TODO *)

let rec get_ty_lbl = function
  | Uast.PTtyapp (Qpreid preid, []) -> keyword preid.pid_str
  | Uast.PTtyapp (_name, hd :: _tl) -> get_ty_lbl hd
  (*
  | PTtyvar of Preid.t
  | PTtuple of pty list
  | PTarrow of labelled_arg * pty * pty
  *)
  | _ -> assert false (* TODO *)

let rec pty_to_ty = function
  | Uast.PTtyapp (id, tys) ->
    TyApp (keyword (id_to_string id), to_ty_list tys)
  | _ -> assert false
and to_ty_list = function
  | [] -> []
  | t :: tl -> pty_to_ty t :: to_ty_list tl

let rec to_args = function
  | [] -> []
  | (_, preid, pty) :: tl ->
    let ty = pty_to_ty pty in
    let str = get_ty_lbl pty in
    (if List.mem str !types
      then (preid.Identifier.Preid.pid_str, ty)
      else (preid.Identifier.Preid.pid_str, TyApp ("Ref", []))
    ) :: to_args tl

let rec get_spec_fields = function
  | [] -> []
  | hd :: tl ->
    (hd.Uast.f_preid.pid_str, pty_to_ty hd.Uast.f_pty) :: get_spec_fields tl

let to_const = function
  | Parsetree.Pconst_integer (n, _char_opt) ->
    CInt (int_of_string n) (* TODO *)
  (*
  | Pconst_char of char
  | Pconst_string of label * location * label option
  | Pconst_float of label * char option
  *)
  | _ -> assert false (* TODO *)

let to_binop = function
  | Uast.Tand | Tand_asym -> BAnd
  | Tor | Tor_asym -> BOr
  | Timplies -> BImpl
  | Tiff -> assert false

let rec to_term term =
  match term.Gospel.Uast.term_desc with
  | Ttrue  -> TBool true
  | Tfalse -> TBool false
  | Tconst c -> TConst (to_const c)
  | Tbinop (t1, binop, t2) ->
    TBinop (to_term t1, to_binop binop, to_term t2)
  | Tinfix (t1, infix, t2) ->
    TInfix (to_term t1, keyword infix.pid_str, to_term t2)
  | Tpreid id ->
    (match id_to_string id with
    | "empty" | "Sequence.empty" -> TSeq (TEmpty (TyVar "Int"))
    | "Nil" -> TVar("Nil()") (* Todo: universel version*)
    | default -> TVar default
    )
  | Tfield (t, field_id) ->
    TField ((to_term t), id_to_string field_id)
  | Tapply (_hd, _t) ->
    let rec aux e : Gospel.Uast.term list= match e.Gospel.Uast.term_desc with
    | Tapply (t1, t2) -> (aux t1) @ [t2]
    | _ -> [e] in
    let tl = aux term in
    let fun_name = (match (List.hd tl).term_desc with
    | Tpreid s -> id_to_string s
    | _ -> assert false) in
    let args = List.tl (to_term_list tl) in
    (match fun_name with
    | "get" | "Sequence.get" ->
      (match args with
      | [n; num] -> TSeq (TGet (n, num))
      | _ -> assert false)
    | "length" | "Sequence.length" -> TSeq (TLength (List.hd args))
    | "tl" | "Sequence.tl"     ->
      TSeq (TSub (List.hd args, (TConst (CInt 1)), None))
    | "hd" | "Sequence.hd"     ->
      TSeq (TGet (List.hd args, (TConst (CInt 0))))
    | "singleton" | "Sequence.singleton" -> TSeq (TSingleton (List.hd args))
    | "cons" | "Sequence.cons" ->
      (match args with
      | [x; seq] -> TSeq (TConcat (TSeq (TSingleton x), seq))
      | _ -> assert false)
    | default  -> TApp (None, default, args))
  | Tlet (name, t1, t2) ->
    TLet (name.pid_str, to_term t1, to_term t2)
  | Tif (tif, tthen, telse) ->
    TTernary (to_term tif, to_term tthen, to_term telse)
  | Tidapp (id, ts) ->
    let str = id_to_string id in
    if String.starts_with ~prefix:"mixfix" str then
      (match str, ts with
      | "mixfix [_]",    [name; t2] ->
        TSeq (TGet (to_term name, to_term t2))
      | "mixfix [_.._]", [name; min; max] ->
        TSeq (TSub (to_term name, to_term min, Some(to_term max)))
      | "mixfix [.._]",  [name; max] ->
        TSeq (TSub (to_term name, TConst (CInt 0), Some(to_term max)))
      | "mixfix [_..]",  [name; min] ->
        TSeq (TSub (to_term name, to_term min, None))
      | _ -> assert false)
    else (match ts with
    | [t1; t2] ->
      TInfix (to_term t1, keyword (id_to_string id), to_term t2)
    | _ -> assert false)
  | Tpoints (Qpreid id, fields) ->
    let mk_acc (field, _) = match field with
      | Uast.Qdot _ -> assert false (* TODO *)
      | Qpreid field ->
        Identifier.Preid.(TAcc (TVar(id.pid_str), field.pid_str)) in
    let mk_and = function
      | [] -> assert false
      | field :: xs ->
        List.fold_left (fun acc f -> TBinop (acc, BAnd, f)) field xs in
    let fields_acc = List.rev (List.map mk_acc fields) in
    mk_and fields_acc
  | Tpoints (Qdot _, _) -> assert false (* TODO *)
  | Told t -> TOld (to_term t)
  | Tunfolding (t1, t2) -> TUnfolding (to_term t1, to_term t2)
  | Tcase (t, (pat, term) :: []) ->
    let pat_name, arg =
      match pat.Uast.pat_desc with
      | Uast.Papp (q, pat_list) ->
        id_to_string q,
        List.map (fun p ->
        match p.Uast.pat_desc with
        | Uast.Pvar v -> v.pid_str
        | _ -> assert false
    ) pat_list
      (*
      | Uast.Pwild -> assert false
      | Uast.Pvar _ -> assert false
      | Uast.Prec _ -> assert false
      | Uast.Ptuple _ -> assert false
      | Uast.Pas _ -> assert false
      | Uast.Por _ -> assert false
      | Uast.Pcast _ -> assert false
      *)
      | _ -> assert false
    in
    TBinop(
    TField((to_term t), String.cat "is" pat_name),
    BAnd,
    TLet(List.hd arg, TField((to_term t), cons_name), (to_term term)))
  | Tcase (_, _) -> assert false
  (*
  | Tnot of term
  | Tquant of quant * binder list * term
  | Tattr of string * term
  | Tcase of term * (pattern * term) list
  | Tcast of term * pty
  | Ttuple of term list
  | Trecord of (qualid * term) list
  | Tupdate of term * (qualid * term) list
  | Tscope of qualid * term
  *)
  | _ -> assert false
and to_term_list (tl : Gospel.Uast.term list) : term list =
  match tl with
  | [] -> []
  | hd :: tl -> to_term hd :: to_term_list tl

let to_body = function
  | None -> None
  | Some term -> Some (to_term term)

let to_spec = function
  | None -> {spec_pre = []; spec_post = [];}
  | Some spec ->
    {spec_pre  = List.map to_term spec.Gospel.Uast.fun_req;
     spec_post = List.map to_term spec.Gospel.Uast.fun_ens}

let ppat_to_str = function
  | Parsetree.Ppat_var str_loc -> str_loc.txt
  (*
  | Ppat_any
  | Ppat_alias of pattern * string loc
  | Ppat_constant of constant
  | Ppat_interval of constant * constant
  | Ppat_tuple of pattern list
  | Ppat_construct of Longident.t loc * (string loc list * pattern) option
  | Ppat_variant of label * pattern option
  | Ppat_record of (Longident.t loc * pattern) list * closed_flag
  | Ppat_array of pattern list
  | Ppat_or of pattern * pattern
  | Ppat_constraint of pattern * core_type
  | Ppat_type of Longident.t loc
  | Ppat_lazy of pattern
  | Ppat_unpack of string option loc
  | Ppat_exception of pattern
  | Ppat_extension of extension
  | Ppat_open of Longident.t loc * pattern
  *)
  | _ -> assert false (* TODO *)

let rec longident_to_str = function
  | Longident.Lident s -> s
  | Ldot (t, s) -> longident_to_str t ^ "DOT" ^ s (* TODO *)
  | Lapply (t1, t2) ->
    longident_to_str t1 ^ "APPLY" ^ longident_to_str t2 (* TODO *)

let rec ptyp_to_ty = function
  | Parsetree.Ptyp_constr (idloc, []) ->
    let str = keyword (longident_to_str idloc.txt) in
    TyApp (str, []) (* TODO for multiple types like Seq[Int] *)
  | Ptyp_poly (_, ty) -> ptyp_to_ty ty.ptyp_desc
  | _  -> assert false

let constraint_to_lbl_ty pattern =
  match pattern.Parsetree.ppat_desc with
  | Parsetree.Ppat_constraint (pattern, ty) ->
    Some (ppat_to_str pattern.ppat_desc, ptyp_to_ty ty.ptyp_desc)
  | Ppat_construct (_, None) -> None
  | Ppat_construct (_, _some) -> assert false
  | Ppat_var str_loc -> Some (str_loc.txt, TyEmpty)
  | _ -> failwith "ERROR: Constraint required"

let rec unstack_expr expr acc =
  match expr.Uast.spexp_desc with
  | Sexp_fun (_, _, pattern, pexp_desc, _) ->
    (match constraint_to_lbl_ty pattern with
    | Some val_ty -> unstack_expr pexp_desc (val_ty :: acc)
    | None -> unstack_expr pexp_desc acc)
  | Sexp_constraint (expr, ty) -> acc, expr, Some ([core_type_to_ty ty])
  | _ -> acc, expr, None

let rec to_expr expr =
  match expr.Uast.spexp_desc with
  | Sexp_constant c -> EConst (to_const c)
  | Sexp_construct (id, _) ->
    (match longident_to_str id.Location.txt with
    | "Nil" -> ENull
    | "()" -> ESkip
    | default -> EVariable default)
  | Sexp_ident id -> EVariable (longident_to_str id.txt)
  | Sexp_let (_, binding :: _and, e2) ->
    let e1 = binding.spvb_expr in
    (match constraint_to_lbl_ty binding.spvb_pat with
    | Some (let_name, let_ty) ->
      ESequence (
        ESequence (
          EVar (let_name, let_ty), to_expr_ret e1 (EVariable let_name)
        ),to_expr e2 )
    | None -> failwith "constraint is None")
  | Sexp_let (_rec, [], _expr) -> assert false
  | Sexp_setfield (e1, id, e2) ->
    EAssig (EField (to_expr e1, longident_to_str id.txt), to_expr e2)
  | Sexp_sequence (e1, e2) -> ESequence (to_expr e1, to_expr e2)
  | Sexp_ifthenelse (eif, ethen, eelse_opt) ->
    EIf (to_expr eif, to_expr ethen,
      match eelse_opt with | None -> None | Some eelse -> Some (to_expr eelse))
  | Sexp_apply (e1, exprs) ->
    (match e1.spexp_desc with
    | Sexp_ident id ->
      let fun_name = keyword (longident_to_str id.txt) in
      (match exprs, fun_name with
      | [(_, e1); (_, e2)], infix when is_infix infix ->
        EInfix (to_expr e1, infix, to_expr e2)
      | exprs, fun_name ->
        let expr_l = List.map (fun (_, e) -> to_expr e) exprs in
        EApp (fun_name, expr_l))
    | _ -> assert false)
  | Sexp_assert e -> EAssert (to_expr e)
  | Sexp_field (e, id) -> EField (to_expr e, longident_to_str id.txt)
  | Sexp_viper_call (opt, expr) -> (match opt with
    | None -> failwith "No gospel attributes"
    | Some t ->
      let call_viper = (match t.keyword with
      | Uast.Fold -> EFold (term_to_expr t.desc)
      | Uast.Unfold -> EUnfold (term_to_expr t.desc)
      | Uast.Apply  -> (term_to_expr t.desc) ) in
      ESequence (call_viper, to_expr expr)
    )
  (*
  | Sexp_function of s_case list
  | Sexp_fun of
      arg_label
      * s_expression option
      * Parsetree.pattern
      * s_expression
      * fun_spec option
  | Sexp_match of s_expression * s_case list
  | Sexp_try of s_expression * s_case list
  | Sexp_tuple of s_expression list
  | Sexp_variant of label * s_expression option
  | Sexp_record of (Longident.t loc * s_expression) list * s_expression option
  | Sexp_array of s_expression list
  | Sexp_while of s_expression * s_expression * loop_spec option
  | Sexp_for of
      Parsetree.pattern
      * s_expression
      * s_expression
      * direction_flag
      * s_expression
      * loop_spec option
  | Sexp_constraint of s_expression * core_type
  | Sexp_coerce of s_expression * core_type option * core_type
  | Sexp_send of s_expression * label loc
  | Sexp_new of Longident.t loc
  | Sexp_override of (label loc * s_expression) list
  | Sexp_letmodule of string option loc * module_expr * s_expression
  | Sexp_letexception of extension_constructor * s_expression
  | Sexp_assert of s_expression
  | Sexp_lazy of s_expression
  | Sexp_poly of s_expression * core_type option
  | Sexp_object of class_structure
  | Sexp_newtype of string loc * s_expression
  | Sexp_pack of s_module_expr
  | Sexp_open of open_declaration * s_expression
  | Sexp_letop of letop
  | Sexp_extension of extension
  | Sexp_unreachable
  *)
  | _ -> assert false (* TODO *)
and to_expr_ret expr ret_val =
  match expr.Uast.spexp_desc with
  | Sexp_record (elems, _) ->
    let lbld_exprs = List.map (fun (id, expr) ->
      longident_to_str id.Location.txt, to_expr expr) elems in
    let seq_expr   = List.fold_left (fun acc (lbl, expr) ->
      ESequence (
        acc, EAssig (EField (ret_val, lbl), expr))) ESkip lbld_exprs in
    let evars = List.map (fun (evar, _) -> EVariable(evar)) lbld_exprs in
    ESequence (EAssig (ret_val, ENew evars), seq_expr)
  | Sexp_constant c ->
    EAssig (ret_val, EConst (to_const c))
  | Sexp_let (_, binding :: _and, e2) ->
    let e1 = binding.spvb_expr in
    (match constraint_to_lbl_ty binding.spvb_pat, ret_val with
    | Some (let_name, let_ty), EVariable ret_val_str ->
      if let_name = ret_val_str then
        ESequence (to_expr_ret e1 (EVariable let_name), to_expr_ret e2 ret_val)
      else
      ESequence (
        ESequence (
          EVar (let_name, let_ty), to_expr_ret e1 (EVariable let_name)
        ), to_expr_ret e2 ret_val)
    | _, _ -> failwith "constraint is None")
  | Sexp_let (_rec, [], _expr) -> assert false
  | Sexp_ident id ->
    (match ret_val, longident_to_str id.txt with
    | EVariable str, id_txt when str = id_txt -> ESkip
    | ret_val, id_txt -> EAssig (ret_val, EVariable id_txt))
  | Sexp_constraint (expr, _ty) -> to_expr_ret expr ret_val
  | Sexp_field (expr, id) ->
    EAssig (ret_val, EField (to_expr expr, longident_to_str id.txt))
  | Sexp_ifthenelse (eif, ethen, eelse_opt) ->
    EIf (to_expr eif, to_expr_ret ethen ret_val,
      match eelse_opt with
      | None -> None | Some eelse -> Some (to_expr_ret eelse ret_val))
  | Sexp_apply (e1, exprs) ->
    let infix = (match e1.spexp_desc with
    | Sexp_ident id -> keyword (longident_to_str id.txt)
    | _ -> failwith "should be a infix operator") in
    (match exprs with
    | [(_, e1); (_, e2)] ->
      EAssig (ret_val, EInfix (to_expr e1, infix, to_expr e2))
    | _ -> assert false)
  | Sexp_construct (_id_loc, expr_opt) -> (match expr_opt with
    | None -> ENull (* TODO *)
    | Some expr -> to_expr_ret expr ret_val)
  | Sexp_assert expr -> EAssert (to_expr expr)
  | Sexp_viper_call (opt, expr) -> (match opt with
    | None -> failwith "No gospel attributes"
    | Some t ->
      let call_viper = (match t.keyword with
      | Uast.Fold -> EFold (term_to_expr t.desc)
      | Uast.Unfold -> EUnfold (term_to_expr t.desc)
      | Uast.Apply  -> (term_to_expr t.desc) ) in
      ESequence (call_viper, to_expr_ret expr ret_val)
  )
  | Sexp_sequence (e1, e2) -> ESequence (to_expr_ret e1 ret_val, to_expr_ret e2 ret_val) (* to_expr_ret or to_expr ?? *)
  | Sexp_setfield (e1, id, e2) ->
    EAssig (EField (to_expr e1, longident_to_str id.txt), to_expr e2)
(*
  | Sexp_function _ -> assert false
  | Sexp_fun _ -> assert false
  | Sexp_match _ -> assert false
  | Sexp_try _ -> assert false
  | Sexp_tuple _ -> assert false
  | Sexp_variant _ -> assert false
  | Sexp_array _ -> assert false
  | Sexp_while _ -> assert false
  | Sexp_for _ -> assert false
  | Sexp_coerce _ -> assert false
  | Sexp_send _ -> assert false
  | Sexp_new _ -> assert false
  | Sexp_setinstvar _ -> assert false
  | Sexp_override _ -> assert false
  | Sexp_letmodule _ -> assert false
  | Sexp_letexception _ -> assert false
  | Sexp_lazy _ -> assert false
  | Sexp_poly _ -> assert false
  | Sexp_object _ -> assert false
  | Sexp_newtype _ -> assert false
  | Sexp_pack _ -> assert false
  | Sexp_open _ -> assert false
  | Sexp_letop _ -> assert false
  | Sexp_extension _ -> assert false
  | Sexp_unreachable -> assert false *)
  | _ -> assert false (* TODO *)

let to_meth_body body = function
  | [] -> to_expr body
  | (lbl, _) :: _ -> to_expr_ret body (EVariable lbl)

let to_str_list lbl_arg_list =
  List.map (function
    | Uast.Lunit -> ""
    | Lnone s -> s.pid_str
    | Loptional s -> s.pid_str
    | Lnamed s -> s.pid_str
    | Lghost _ -> assert false
  ) lbl_arg_list

let rec get_ghost_args args =
  match args with
  | [] -> []
  | arg :: tl ->
    (match arg with
    | Uast.Lghost (name, pty) -> [name.pid_str, pty_to_ty pty]
    | _ -> []) @ get_ghost_args tl

let get_gargs_ret_pre_post = function
  | None   -> [], None, [], []
  | Some s ->
    let ghost_args, val_ret = (match s.Uast.sp_header with
    | None   -> [], None
    | Some h ->
      get_ghost_args h.sp_hd_args,
      match to_str_list h.sp_hd_ret with
      | [] -> None
      | _  -> Some (to_str_list h.sp_hd_ret)) in
    ghost_args, val_ret, List.map to_term s.sp_pre, List.map to_term s.sp_post

let merge_returns ret_names_opt tys_opt =
  match ret_names_opt, tys_opt with
  | None, None -> []
  | Some ret_names, Some tys ->
    (try List.map2 (fun name -> fun ty -> name, ty) ret_names tys
     with Invalid_argument _ -> assert false)
  | _ -> failwith "ERROR: Not the same amount of parameters and type"

let struct_desc = function
  | Uast.Str_type (_recf, ty_decl :: _ands) ->
    (* For the moment, no "and" in type declaration *)
    let _models = (match ty_decl.tspec with
    | None -> []
    | Some spec -> get_spec_fields spec.ty_field) in
    let r = to_type_def ty_decl in
    r
  | Str_function f ->
    let args = to_args f.fun_params in
    (match f.fun_type with
    | None ->
      [DPredicate {
        pred_name = f.fun_name.pid_str;
        pred_body = to_body f.fun_def;
        pred_args = args;
      }]
    | Some ret_ty -> [DFunction {
        function_name = f.fun_name.pid_str;
        function_args = args;
        function_rety = pty_to_ty ret_ty;
        function_spec = to_spec f.fun_spec;
        function_body = to_body f.fun_def;
    }])
    | Str_value (_rec_f, [{spvb_pat; spvb_expr; spvb_vspec;_}]) ->
      let args, body, tys_opt = unstack_expr spvb_expr [] in
      let ghost_args, ret_names_opt, pre, post =
        get_gargs_ret_pre_post spvb_vspec in
      let returns = merge_returns ret_names_opt tys_opt in
      [DMethod {
        method_name = ppat_to_str spvb_pat.ppat_desc;
        method_args = (List.rev args) @ ghost_args;
        method_returns = returns;
        method_spec = {
          spec_pre  = pre;
          spec_post = post;
        };
        method_body = Some (to_meth_body body returns);
      }]
    | Str_value (_rec_f, _) -> assert false
    (* For the moment, no "and" in type declaration *)
  (*
  | Str_eval of s_expression * attributes
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
  | _ -> assert false (* TODO *)

let cameleer_structure_item i = struct_desc i.Uast.sstr_desc

let cameleer_structure (s: Uast.s_structure) =
  List.flatten (List.map (fun item -> cameleer_structure_item item) s)

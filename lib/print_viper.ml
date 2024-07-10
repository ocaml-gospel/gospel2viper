open PPrint
open Viper_ast

let sprintf format = Printf.ksprintf arbitrary_string format
let run (print : Buffer.t -> 'a -> unit) (x : 'a) : string =
  let b = Buffer.create 1024 in
  print b x;
  Buffer.contents b

(* Requirements *)
let indentation = 2
let width = ref 80

(* Definition of useful symbols and keywords *)
let commaspace = string ", "
let colonspace = string ": "
let spaceconcatspace = string " ++ "
let dotdot = string ".."
let dot = string "."
let implies = string "==>" ^^ break 1
let crlet = string "let "
let spaceeqspace = string " == "
let spaceinspace = string " in "
let notspace = string "not "
let ifspace = string "if "
let spaceelsespace = string " else "
let spaceintmarkspace = string " ? "
let spacecolonspace = string " : "
let not = string "!"
let minus = string "!"
let varspace = string "var "
let spaceandandspace = string " && "
let ttrue = string "true"
let null = string "null"
let ffalse = string "false"
let reqspace = string "requires "
let nnew = string "new"
let spaceassignspace = string " := "
let ensspace = string "ensures "
let methspace = string "method "
let funspace = string "function "
let predspace = string "predicate "
let acc = string "acc"
let spacereturnsspace = break 1 ^^ string "returns "

(* Definition of blocks around document d *)
let block n opening contents closing =
  group (opening ^^ nest n contents ^^ closing)
let block = block indentation
let parens   d = block lparen   (break 0 ^^ d) (break 0 ^^ rparen)
let brackets d = block lbracket (break 0 ^^ d) (break 0 ^^ rbracket)
let braces   d = block lbrace   (break 1 ^^ d) (break 1 ^^ rbrace)
let pipes    d = (string "|") ^^ d ^^ (string "|")

(* Printers for Viper's AST *)
let rec pp_list pp_elem = function
  | [] -> empty
  | elem :: [] -> pp_elem elem
  | elem :: tl -> pp_elem elem ^^ commaspace ^^ pp_list pp_elem tl

let pp_binop = function
  | BAnd  -> string "&&"
  | BOr   -> string "||"
  | BImpl -> string "==>"

let pp_const = function
  | CInt n -> string (string_of_int n)

let rec pp_ty = function
  | TyApp (s, tys) ->
    string s ^^ (if tys == [] then empty else brackets (pp_list pp_ty tys))
  | TyVar s -> string s
and pp_term = function
  | TConst n -> pp_const n
  | TBool  b -> if b then ttrue else ffalse
  | TNull -> null
  | TApp (_ty_opt, s, terms) ->
    group (string s ^^ parens (pp_list pp_term terms))
  | TVar s -> string s
  | TField (term, field) -> (* TODO : parens if term <> TVar *)
    pp_term term ^^ dot ^^ string field
  | TInfix (term1, symb, term2) ->
    parens (pp_term term1 ^^ space ^^ string symb ^^ space ^^ pp_term term2)
  | TSeq seq -> pp_tseq seq
  | TBinop (t1, symb, t2) ->
    parens (pp_term t1 ^^ space ^^ pp_binop symb ^^ space ^^ pp_term t2)
  | TNeg term -> minus ^^ pp_term term
  | TAcc (term, field) -> (* TODO : parens if term <> TVar *)
    acc ^^ parens (pp_term term ^^ dot ^^ string field)
  | TLet (name, t1, t2) ->
    crlet ^^ string name ^^ spaceeqspace ^^
    parens (pp_term t1) ^^ spaceinspace ^^ pp_term t2
  | TTernary (tif, tthen, telse) ->
    parens (pp_term tif ^^ spaceintmarkspace ^^
    pp_term tthen ^^ spacecolonspace ^^ pp_term telse)
  | TNot term -> notspace ^^ parens (pp_term term)
and pp_tseq = function
  | TEmpty ty -> pp_ty (TyApp("Seq", [ty])) ^^ parens empty
  | TSingleton term -> string "Seq" ^^ parens (pp_term term)
  | TConcat (term1, term2) ->
    pp_term term1 ^^ spaceconcatspace ^^ pp_term term2
  | TLength term -> pipes (pp_term term)
  | TGet (s, term) -> (pp_term s) ^^ brackets (pp_term term)
  | TSub (s, term1, term2_opt) ->
    pp_term s ^^ brackets (pp_term term1 ^^ dotdot ^^ (
    match term2_opt with
    | Some term2 -> pp_term term2
    | None -> empty))

let rec pp_expr = function
  | EConst c -> pp_const c
  | EBool b -> if b then ttrue else ffalse
  | ENull -> null
  | EApp (name, exprs) -> string name ^^ parens (pp_list pp_expr exprs)
  | EVariable name -> string name
  | ENeg expr -> minus ^^ pp_expr expr
  | EBinop (e1, binop, e2) ->
    parens (pp_expr e1 ^^ space ^^ pp_binop binop ^^ space ^^ pp_expr e2)
  | ESeq seq -> pp_eseq seq
  | EInfix (e1, infix, e2) ->
    parens (pp_expr e1 ^^ space ^^ string infix ^^ space ^^ pp_expr e2)
  | EIf (tif, tthen, telse_opt) ->
    ifspace ^^ parens (pp_expr tif) ^^ space ^^ braces (pp_expr tthen) ^^
    (match telse_opt with
    | None -> empty
    | Some telse -> spaceelsespace ^^ braces (pp_expr telse))
  | EField (expr, field) -> (* TODO : parens if term <> TVar *)
    pp_expr expr ^^ dot ^^ string field
  | ENew (exprs) -> nnew ^^ parens (pp_list pp_expr exprs)
  | EAssig (e1, e2) -> pp_expr e1 ^^ spaceassignspace ^^ pp_expr e2
  | EVar (lbl, ty)  -> varspace ^^ string lbl ^^ spacecolonspace ^^ pp_ty ty
  | ESequence (e1, e2) -> pp_expr e1 ^^ hardline ^^ pp_expr e2
and pp_eseq = function
  | EEmpty ty -> pp_ty (TyApp("Seq", [ty])) ^^ parens empty
  | ESingleton expr -> string "Seq" ^^ parens (pp_expr expr)
  | EConcat (expr1, expr2) ->
    pp_expr expr1 ^^ spaceconcatspace ^^ pp_expr expr2
  | ELength expr -> pipes (pp_expr expr)
  | EGet (s, expr) -> (pp_expr s) ^^ brackets (pp_expr expr)
  | ESub (s, expr1, expr2_opt) ->
    pp_expr s ^^ brackets (pp_expr expr1 ^^ dotdot ^^ (
    match expr2_opt with
    | Some expr2 -> pp_expr expr2
    | None -> empty))

let pp_cond prefix conds =
  let rec pp_conds = function
  | [] -> empty
  | h :: [] -> group (pp_term h)
  | h :: t  -> group (pp_term h) ^^ spaceandandspace ^^ group (pp_conds t) in
    prefix ^^ pp_conds conds

let pp_spec (spec: spec) = match spec.spec_pre, spec.spec_post with
  | [], [] -> empty
  | [], post  -> group (pp_cond ensspace post)
  | pre, []   -> group (pp_cond reqspace pre)
  | pre, post ->
    group (pp_cond reqspace pre) ^^ break 1 ^^ group (pp_cond ensspace post)

let rec pp_val_type_list = function
  | [] -> empty
  | (arg_name, arg_type) :: []  ->
    string arg_name ^^ colonspace ^^ pp_ty arg_type
  | (arg_name, arg_type) :: tl  ->
    string arg_name ^^ colonspace ^^ pp_ty arg_type ^^
    (if tl = [] then empty else commaspace) ^^ pp_val_type_list tl

let pp_args args = parens (pp_val_type_list args)

let pp_returns returns =
  if returns = [] then empty
  else spacereturnsspace ^^ parens (pp_val_type_list returns)

let pp_expr_body = function
  | None -> empty
  | Some el -> braces (
    let rec iter = function
    | [] -> empty
    | elem :: [] -> pp_expr elem
    | elem :: tl -> pp_expr elem ^^ hardline ^^ iter tl in
    iter el
    )

let pp_method_def m =
    methspace ^^ string m.method_name ^^ pp_args m.method_args ^^
    pp_returns m.method_returns ^^
    hardline ^^ pp_spec m.method_spec ^^ pp_expr_body m.method_body

let pp_term_body = function
  | None   -> empty
  | Some t -> braces (pp_term t)

let pp_predicate_def p =
  predspace ^^ string p.pred_name ^^ pp_args p.pred_args ^^
  space ^^ pp_term_body p.pred_body

let pp_function_def f =
  funspace ^^ string f.function_name ^^ pp_args f.function_args ^^
  colonspace ^^ pp_ty f.function_rety ^^ space ^^
  pp_spec f.function_spec ^^ space ^^ pp_term_body f.function_body

let pp_decl = function
  | DPredicate pred_def -> pp_predicate_def pred_def
  | DMethod method_def  -> pp_method_def method_def
  | DFunction function_def -> pp_function_def function_def
  | DField (name, ty) ->
      string "field" ^^ space ^^ string name ^^ colonspace ^^ pp_ty ty
  | DBlank -> empty

let is_blank = function | DBlank -> true | _ -> false

let rec pp_decls = function
  | [] -> empty
  | d :: [] -> pp_decl d
  | d :: decls when is_blank d -> pp_decls decls
  | d :: decls -> group (pp_decl d) ^^ hardline ^^ hardline ^^ pp_decls decls

let pp_program p = pp_decls p

let print v: string = run (PPrint.ToBuffer.pretty 0.9 !width) (pp_program v)

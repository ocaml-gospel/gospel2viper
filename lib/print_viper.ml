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
let not = string "!"
let spaceandandspace = string " && "
let reqspace = string "requires "
let ensspace = string "ensures "
let methspace = string "method "
let predspace = string "predicate "
let spacereturnsspace = break 1 ^^ string "returns "

(* Definition of blocks around document d *)
let block n opening contents closing =
  group (opening ^^ nest n contents ^^ closing)
let block = block indentation
let parens d   = block lparen   (break 0 ^^ d) (break 0 ^^ rparen)
let brackets d = block lbracket (break 0 ^^ d) (break 0 ^^ rbracket)
let braces d   = block lbrace   (break 1 ^^ d) (break 1 ^^ rbrace)

(* Printers for Viper's AST *)
let rec pp_list pp_elem = function
  | [] -> empty
  | elem :: [] -> pp_elem elem
  | elem :: tl -> pp_elem elem ^^ commaspace ^^ pp_list pp_elem tl

let pp_op = function
  | BAnd -> string "&&"
  | BOr  -> string "||"

let rec pp_ty = function
  | TyApp (s, tys) ->
    string s ^^ (if tys == [] then empty else brackets (pp_list pp_ty tys))
  | TyVar s -> string s
and pp_term = function
  | TConst n -> string (string_of_int n)
  | TBool  b -> if b then string "true" else string "false"
  | TApp (_ty_opt, s, terms) ->
    group (string s ^^ parens (pp_list pp_term terms))
  | TVar s -> string s
  | TInfix (term1, symb, term2) ->
    parens (pp_term term1 ^^ space ^^ string symb ^^ space ^^ pp_term term2)
  | TSeq seq -> pp_tseq seq
  | TBinop (t1, symb, t2) -> parens (pp_term t1 ^^ space ^^ pp_op symb ^^ space ^^ pp_term t2)
  | TNot term -> not ^^ pp_term term
and pp_tseq = function
  | TEmpty ty -> pp_ty (TyApp("Seq", [ty])) ^^ parens empty
  | TSingleton term -> string "Seq" ^^ parens (pp_term term)
  | TConcat (term1, term2) -> pp_term term1 ^^ spaceconcatspace ^^ pp_term term2
  | TGet (s, term) -> string s ^^ brackets (pp_term term)
  | TSub (s, term1, term2_opt) ->
    pp_term s ^^ brackets (pp_term term1 ^^ dotdot ^^ (
    match term2_opt with
    | Some term2 -> pp_term term2
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
  | pre, post -> group (pp_cond reqspace pre) ^^ break 1 ^^ group (pp_cond ensspace post)

let rec pp_val_type_list = function
  | [] -> empty
  | (arg_name, arg_type) :: [] -> string arg_name ^^ colonspace ^^ pp_ty arg_type
  | (arg_name, arg_type) :: tl  ->
    string arg_name ^^ colonspace ^^ pp_ty arg_type ^^
    (if tl = [] then empty else commaspace) ^^ pp_val_type_list tl

let pp_args args = parens (pp_val_type_list args)

let pp_returns returns =
  if returns = [] then empty else spacereturnsspace ^^ parens (pp_val_type_list returns)

let pp_method_def m =
  prefix 2 1
    (group (methspace ^^ string m.method_name ^^ pp_args m.method_args ^^ pp_returns m.method_returns))
    (pp_spec m.method_spec)

let pp_body = function
  | None   -> empty
  | Some t -> pp_term t

let pp_predicate_def p =
  predspace ^^ string p.pred_name ^^ pp_args p.pred_args ^^ pp_body p.pred_body

let pp_decl = function
  | DPredicate pred_def -> pp_predicate_def pred_def
  | DMethod method_def  -> pp_method_def method_def

let rec pp_decls = function
  | [] -> empty
  | d :: [] -> pp_decl d
  | d :: decls -> group (pp_decl d) ^^ hardline ^^ hardline ^^ pp_decls decls

let pp_program p = pp_decls p

let print v: string = run (PPrint.ToBuffer.pretty 0.9 !width) (pp_program v)
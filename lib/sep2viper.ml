open Gospel
open Sep_ast
open Viper_ast
open Symbols

let keywords_map = function
  | "loc" -> "Ref"
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
  (*
  | "infix ++" -> "app" *)
  | default -> default

let to_binop (op: Tterm.binop) : binop = match op with
  | Tand | Tand_asym -> BAnd
  | Tor  | Tor_asym  -> BOr
  (*
  | Timplies
  | Tiff *)
  | _ -> assert false

let rec to_ty (ttypety: Ttypes.ty) : ty =
  match ttypety.ty_node with
  | Tyvar tvsymb -> TyVar tvsymb.tv_name.id_str
  | Tyapp (tysymb, tys) ->
    TyApp (keywords_map tysymb.ts_ident.id_str , to_ty_list tys)
and to_ty_list = function
    | [] -> []
    | t :: tl -> to_ty t :: to_ty_list tl

let to_args (l: Symbols.vsymbol list) =
  List.map (fun e -> e.vs_name.id_str, to_ty e.vs_ty) l

let rec to_args_opt (opt_l: Symbols.vsymbol option list) : (string * ty) list =
  match opt_l with
  | [] -> []
  | v_opt :: l ->
    match v_opt with
    | Some e -> (e.vs_name.id_str, to_ty e.vs_ty) :: to_args_opt l
    | None -> []

let to_int ?(neg = false) (c: Parsetree.constant) : int =
  match c with
  | Pconst_integer (s, _) -> int_of_string (if neg then "-" ^ s else s)
  (*
  | Pconst_char of char
  | Pconst_string of label * location * label option
  | Pconst_float of label * char option *)
  | _ -> assert false

let is_true bsymb = bsymb.ls_name.id_str = "true"
let is_false bsymb = bsymb.ls_name.id_str = "false"

let rec to_term (t: Tterm.term) : term =
  match t.t_node with
  | Tvar vsymb -> TVar vsymb.vs_name.id_str
  | Tconst c -> TConst (to_int c)
  | Tapp (_, b, []) when is_true  b -> TBool true
  | Tapp (_, b, []) when is_false b -> TBool false
  | Tapp (_, lsymb, terms)
  when lsymb.ls_name.id_path = ["Gospelstdlib"; "Sequence"] ->
    TSeq (to_seq lsymb terms)
  | Tapp (_, lsymb, [t1; t2])
  when String.starts_with ~prefix:"infix" lsymb.ls_name.id_str ->
    TInfix (to_term t1, keywords_map lsymb.ls_name.id_str, to_term t2)
  | Tapp (_, lsymb, [t])
  when String.starts_with ~prefix:"prefix" lsymb.ls_name.id_str ->
    (match t.t_node with
    | Tconst c -> TConst (to_int ~neg:true c)
    | _ -> assert false)
  | Tapp (_, lsymb, [e])
  when lsymb.ls_name.id_str = "integer_of_int" -> to_term e
  | Tapp (_, lsymb, terms) ->
    Format.printf "%s@." lsymb.ls_name.id_str;
    TApp (None, lsymb.ls_name.id_str, to_term_list terms)
  | Tbinop (binop, t1, t2) ->
    TBinop (to_term t1, to_binop binop, to_term t2)
  | Tnot t -> TNot (to_term t)
  (*
  | Tfield of term * lsymbol
  | Tif of term * term * term
  | Tlet of vsymbol * term * term
  | Tcase of term * (pattern * term option * term) list
  | Tquant of quant * vsymbol list * term
  | Tlambda of pattern list * term
  | Told of ter *)
  | _ -> assert false
and to_term_list (ts: Tterm.term list) : term list =
  match ts with
  | [] -> []
  | term :: tl -> to_term term :: to_term_list tl
and to_seq lsymb terms : tseq =
  match lsymb.ls_name.id_str, terms with
  | "empty", [] -> TEmpty (TyApp ("Int", []))
  | "cons", [fst; snd] -> TConcat (TSeq (TSingleton (to_term fst)), to_term snd)
  | "tl", [seq] -> TSub (to_term seq, (TConst 1), None)
  | "hd", [seq] -> TGet (to_term seq, (TConst 0))
  | "length", [seq] -> TLength (to_term seq)
  | _ -> assert false

let rec of_sep_term_list (s: sep_term list) : term list =
  match s with
  | [] -> []
  | st :: sep_terms ->
    match st with
    | Pure t -> to_term t :: of_sep_term_list sep_terms
    | App (lsymb, terms) ->
      let lsymb_str = lsymb.ls_name.id_str in
      if lsymb_str = "Int" then of_sep_term_list sep_terms else
      TApp (None, lsymb_str, to_term_list terms) :: of_sep_term_list sep_terms

let sep_def d =
  match d.d_node with
  | Pred rep_pred -> DPredicate {
    pred_name = rep_pred.pred_name.id_str;
    pred_body = None;
    pred_args = to_args rep_pred.pred_args; }
  | Triple t ->
      let post_exists, sep_term_list = (match t.triple_post with
      | exists, sep_term_list -> exists, sep_term_list) in
    DMethod {
    method_name = t.triple_name.id_str;
    method_args = to_args t.triple_vars;
    method_returns = to_args (post_exists @ t.triple_rets);
    method_spec = {
      spec_pre = of_sep_term_list t.triple_pre;
      spec_post = of_sep_term_list sep_term_list; }}
  | Type _ -> DBlank
  (*
  | Type of Ident.t * Ttypes.tvsymbol list  (** Type definition *)
  | Axiom of Tast.axiom  (** Axiom *)
  | Function of Tast.function_  (** Logical Function *)
  | Module of Ident.t * definition list *)
  | _ -> assert false

let sep_defs d = List.map (fun decl -> sep_def decl) d
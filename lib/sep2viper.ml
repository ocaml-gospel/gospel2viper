open Gospel
open Sep_ast
open Viper_ast
open Symbols

let name = function
  | "loc" -> "Ref"
  | "int" -> "Int"
  | "sequence" -> "Seq"
  | default -> default

let rec to_ty (ttypety: Ttypes.ty) : ty =
  match ttypety.ty_node with
  | Tyvar tvsymb -> TyVar tvsymb.tv_name.id_str
  | Tyapp (tysymb, tys) ->
    TyApp (name tysymb.ts_ident.id_str , to_ty_list tys)
and to_ty_list = function
    | [] -> []
    | t :: tys -> to_ty t :: to_ty_list tys

let to_args (l: Symbols.vsymbol list) =
  List.map (fun e -> e.vs_name.id_str, to_ty e.vs_ty) l

let rec to_args_opt (opt_l: Symbols.vsymbol option list) : (string * ty) list =
  match opt_l with
  | [] -> []
  | v_opt :: l ->
    match v_opt with
    | Some e -> (e.vs_name.id_str, to_ty e.vs_ty) :: to_args_opt l
    | None -> []

let to_int (c: Parsetree.constant) : int =
  match c with
  | Pconst_integer (s, _) -> int_of_string s
  (*
  | Pconst_char of char
  | Pconst_string of label * location * label option
  | Pconst_float of label * char option *)
  | _ -> assert false

let rec to_term (t: Tterm.term) : term =
  match t.t_node with
  | Tvar vsymb -> TVar vsymb.vs_name.id_str
  | Tconst c -> TConst (to_int c)
  | Tapp (lsymb, terms) ->
    if lsymb.ls_name.id_path = ["Gospelstdlib"; "Sequence"] then
    TSeq(to_seq lsymb terms)
    else TApp (None, lsymb.ls_name.id_str, to_term_list terms)
  (*
  | Tfield of term * lsymbol
  | Tif of term * term * term
  | Tlet of vsymbol * term * term
  | Tcase of term * (pattern * term option * term) list
  | Tquant of quant * vsymbol list * term
  | Tlambda of pattern list * term
  | Tbinop of binop * term * term
  | Tnot of term
  | Told of ter *)
  | _ -> assert false
and to_term_list (ts: Tterm.term list) : term list =
  match ts with
  | [] -> []
  | t :: terms -> to_term t :: to_term_list terms
and to_seq lsymb terms : tseq =
  match lsymb.ls_name.id_str, terms with
  | "empty", [] -> TEmpty(TyApp("Int", []))
  | "cons", [fst; snd] -> TConcat(TSeq(TSingleton(to_term fst)), to_term snd)
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
  | Pred (id, args) ->
    DPredicate {
    pred_name = id.id_str;
    pred_body = None;
    pred_args = to_args args; }
  | Triple t -> DMethod {
    method_name = t.triple_name.id_str;
    method_args = to_args t.triple_vars;
    method_returns = to_args t.triple_rets;
    method_spec = {
      spec_pre = of_sep_term_list t.triple_pre;
      spec_post = match t.triple_post with
      | _vsymb, sep_term_list -> of_sep_term_list sep_term_list;
    }
  }
  (*
  | Type of Ident.t * Ttypes.tvsymbol list  (** Type definition *)
  | Axiom of Tast.axiom  (** Axiom *)
  | Function of Tast.function_  (** Logical Function *)
  | Module of Ident.t * definition list *)
  | _ -> assert false

let sep_defs d = List.map (fun decl -> sep_def decl) d
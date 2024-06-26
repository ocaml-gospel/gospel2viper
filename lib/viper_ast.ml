type binop = BAnd | BOr

type ty =
  | TyApp of string * (ty list)
  | TyVar of string
and term =
  | TConst of int
  | TBool of bool
  | TApp of ty option * string * term list
  | TVar of string
  | TInfix of term * string * term
  | TSeq of tseq
  | TBinop of term * binop * term
  | TNot of term
  | TField of term * term
and tseq =
  | TEmpty of ty
  | TSingleton of term
  | TConcat of term * term
  | TLength of term
  | TGet of term * term (* TGet seq_name pos *)
  | TSub of term * term * term option (* TSub seq_name start_pos end_pos *)

type spec = {
  spec_pre:  term list;
  spec_post: term list;
}

type predicate_def = {
  pred_name: string;
  pred_body: term option;
  pred_args: (string * ty) list;
}

type method_def = {
  method_name: string;
  method_args: (string * ty) list;
  method_returns: (string * ty) list;
  method_spec: spec;
}

type decl =
  | DPredicate of predicate_def
  | DMethod of method_def
  | DField of string * ty
  | DBlank

type program = decl list
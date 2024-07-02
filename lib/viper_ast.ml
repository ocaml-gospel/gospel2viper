type binop = BAnd | BOr | BImpl

type ty =
  | TyApp of string * (ty list)
  | TyVar of string
and term =
  | TConst of int
  | TBool of bool
  | TApp of ty option * string * term list
  | TVar of term option * string
  | TInfix of term * string * term
  | TSeq of tseq
  | TBinop of term * binop * term
  | TNot of term
  | TAcc of string * string
  | TLet of string * term * term
  | TIf of term * term * term option
  | TTernary of term * term * term
and tseq =
  | TEmpty of ty
  | TSingleton of term
  | TConcat of term * term
  | TLength of term
  | TGet of term * term
  | TSub of term * term * term option

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

type function_def = {
  function_name: string;
  function_args: (string * ty) list;
  function_rety: ty;
  function_spec: spec;
  function_body: term option;
}

type decl =
  | DPredicate of predicate_def
  | DMethod of method_def
  | DFunction of function_def
  | DField of string * ty
  | DBlank

type program = decl list
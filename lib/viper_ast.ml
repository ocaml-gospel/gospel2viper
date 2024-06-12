type ty =
  | TyApp of string * (ty list)
  | TyVar of string
and term =
  | TConst of int
  | TApp of ty option * string * term list
  | TVar of string
  | TInfix of term * string * term
  | TSeq of tseq
and tseq =
  | TEmpty of ty
  | TSingleton of term
  | TConcat of term * term
  | TGet of string * term
  | TSub of string * term * term

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

type program = decl list
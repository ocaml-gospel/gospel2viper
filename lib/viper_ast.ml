type binop = BAnd | BOr | BImpl

type label = string

type ty =
  | TyApp of label * (ty list)
  | TyVar of label

type const = CInt of int

and term =
  | TConst of const
  | TBool of bool
  | TNull
    (* null keyword for null references *)
  | TApp of ty option * label * term list
    (* f(t1, t2, ...) *)
  | TVar of label
  | TField of term * label
    (* t1.t2 *)
  | TInfix of term * string * term
  | TSeq of tseq
  | TBinop of term * binop * term
  | TNeg of term
    (* - t *)
  | TAcc of term * label
    (* acc(t.field) *)
  | TLet of label * term * term
    (* let f = t1 in t2 *)
  | TTernary of term * term * term
    (* bterm ? t1 : t2 *)
  | TNot of term
    (* not t *)
and tseq =
  | TEmpty of ty
    (* Seq[Int]() *)
  | TSingleton of term
    (* Seq(t) *)
  | TConcat of term * term
  | TLength of term
    (* |seq| *)
  | TGet of term * term
    (* [n] *)
  | TSub of term * term * term option
    (* [_.._] *)

and expr =
  | EConst of const
  | EBool of bool
  | ESkip
  | ENull
    (* null keyword for null references *)
  | EApp of label * (expr list)
    (* f(e1, e2, ...) *)
  | EVariable of label
  | ENeg of expr
    (* - t *)
  | EBinop of expr * binop * expr
  | ESeq of eseq
  | EInfix of expr * string * expr
  | EIf of expr * expr * expr option
    (* if (bexpr) {e1} else {e2}
       if (bexpr) {e1}
    *)
  | EVar of label * ty
    (* var t : Int *)
  | EField of expr * label
    (* t.e1 *)
  | ENew of (expr list)
    (* new(e1, e2, ...) *)
  | EAssig of expr * expr
    (* e1 := e2 *)
  | ESequence of expr * expr
     (* e1
        e2 *)
  | EAssert of expr
and eseq =
  | EEmpty of ty
    (* Seq[Int]() *)
  | ESingleton of expr
    (* Seq(t) *)
  | EConcat of expr * expr
  | ELength of expr
    (* |seq| *)
  | EGet of expr * expr
    (* [n] *)
  | ESub of expr * expr * expr option
    (* [_.._] *)

type spec = {
  spec_pre:  term list;
  spec_post: term list;
}

type predicate_def = {
  pred_name: label;
  pred_body: term option;
  pred_args: (label * ty) list;
}

type method_def = {
  method_name: label;
  method_args: (label * ty) list;
  method_returns: (label * ty) list;
  method_spec: spec;
  method_body: expr option;
}

type function_def = {
  function_name: label;
  function_args: (label * ty) list;
  function_rety: ty;
  function_spec: spec;
  function_body: term option;
}

type decl =
  | DPredicate of predicate_def
  | DMethod of method_def
  | DFunction of function_def
  | DField of label * ty
  | DBlank

type program = decl list
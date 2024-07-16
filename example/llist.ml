type llist =
  Nil[@viper "null"] |
  Cons of { mutable value : int; mutable next : llist }
(*@ mutable model view : integer sequence *)

(*@ predicate llist_pred (this: llist) =
    if this <> Nil then
      this ~~> {value; next} &&
      llist_pred this.next
    else true
*)

(*@ function _constr_model_ (t: llist) : int sequence =
    if t = Nil then empty else singleton t.value ++ _constr_model_(t.next) *)
(*@ requires llist_pred t *)


let prepend (x: int) (l: llist) : llist = Cons { value = x; next = l }
(*@ nl = prepend x l
    requires llist_pred l
    ensures  llist_pred nl
    ensures  nl.view = ((singleton x) ++ old(l.view)) *)
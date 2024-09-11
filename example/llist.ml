type llist =
  Nil[@viper "null"] |
  Cons of { mutable value : int; mutable next : llist }

(*@ predicate llist (this: llist) =
    if this <> Nil then
      this ~~> {value; next} &&
      llist this.next
    else true *)

(*@ function constr_model_llist (t: llist) : int sequence =
    if t = Nil then empty else singleton t.value ++ constr_model_llist t.next *)
(*@ requires llist t *)

let prepend (x: int) (l: llist) : llist =
  Cons { value = x; next = l }
(*@ nl = prepend x l
    requires llist l
    ensures  llist nl
    ensures  constr_model_llist nl = ((singleton x) ++ old(constr_model_llist l)) *)
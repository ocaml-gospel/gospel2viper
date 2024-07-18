type t =
  Nil[@viper "null"] |
  Cons of { mutable value : int; mutable next : t }

(*@ predicate lseg (from: t) (to: t) =
    if from <> to then
      from ~~> {value; next} &&
      lseg from.next to
    else true *)

(*@ function constr_model_lseg (from: t) (to: t) : int sequence =
    (* unfolding lseg(from, to) in *)
    if from = to then empty else singleton from.value ++ (constr_model_lseg from.next to) *)
(*@ requires lseg from to *)

type queue = {
  mutable length : int;
  mutable first : t;
  mutable last : t
}

(*@ predicate queue (q: queue) =
      q ~~> {length; first; last} &&
      if q.last = Nil then
        q.first = Nil && q.length = 0
      else
        lseg q.first q.last &&
        lseg q.last Nil *)

(*@ function constr_model_queue (q: queue) : int sequence =
    (* unfolding queue(q) in *)
    if q.last = Nil then empty else (constr_model_lseg q.first q.last) ++ (constr_model_lseg q.last null)  *)
(*@ requires queue q *)

let create () : queue =
  let r : queue = Cons { length = 0; first = Nil; last = Nil } in
  (* fold queue q *)
  r
(*@ q = create ()
      ensures queue q
      ensures (constr_model_queue q) = empty *)

let clear (q: queue) =
  q.length <- 0;
  q.first  <- Nil;
  q.last   <- Nil;
  (* fold queue q *)
  ()
(*@ clear q
    requires queue q
    ensures  queue q
    ensures  (constr_model_queue q) = empty *)

let clear_alt (q: queue) =
  (* unfold queue q *)
  q.length <- 0;
  q.first  <- Nil;
  q.last   <- Nil;
  (* fold queue q *)
  ()
(*@ clear_alt q
    requires q ~~> {length; first; last}
    ensures queue q
    ensures (constr_model_queue q) = empty *)

let add (x: int) (q: queue) =
  let cell : queue = Cons { value = x; next = Nil} in
  if q.last = Nil then (
    q.length <- 1;
    q.first <- cell;
    q.last <- cell)
  else (
    q.length <- q.length + 1;
    q.last.next <- cell;
    q.last <- cell
  )
(*@ add x q
    requires queue q
    ensures  queue q
    ensures  (constr_model_queue q) = ((old (constr_model_queue q)) ++ (singleton x) ) *)

let transfer (q1: queue) (q2: queue) =
  if q1.length > 0 then
    if q2.last = Nil then (
      q2.length <- q1.length;
      q2.first <- q1.first;
      q2.last <- q1.last;
      clear_alt q1)
    else (
      q2.length <- q2.length + q1.length;
      q2.last.next <- q1.first;
      q2.last <- q1.last;
      clear_alt q1)
(*@ transfer q1 q2
    requires queue q1
    requires queue q2
    ensures  queue q1
         &&  constr_model_queue q1 = empty
    ensures  queue q2
         &&  constr_model_queue q2 = ((old (constr_model_queue q2)) ++ (old (constr_model_queue q1))) *)


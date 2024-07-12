type t = Nil[@viper "null"] | Cons of { mutable value : int; mutable next : t }
(*@ mutable model view : integer sequence *)

(*@ predicate lseg (from: t) (l: int sequence) (to: t) =
      if l = empty then from = to
      else
        from ~~> {value; next} &&
        let vv = get l 0 in
        let ll = tl l in
        vv = from.value &&
        lseg from.next ll to *)
type queue = {
  mutable length : int;
  mutable first : t;
  mutable last : t
}

(*@ function take_last (s : int sequence) : int sequence =
      s[.. length s - 1] *)

(*@ function end_seq (s : int sequence) : int sequence =
      let max  = length s - 1 in
      let end = get s max in
      singleton end *)
(*@ requires s <> empty *)

(*@ predicate queue (q: queue) (l: int sequence) =
      q ~~> {length; first; last} &&
      if q.last = Nil then
        l = empty && q.first = Nil && q.length = 0
      else
        length l > 0 && length l = q.length &&
        let ll = take_last l in
        let r = end_seq l in
        lseg q.first ll q.last &&
        lseg q.last r Nil *)

let create () : queue =
  Cons { length = 0; first = Nil; last = Nil }
(*@ q = create ()
      ensures queue q empty *)

let clear (q: queue) =
  q.length <- 0;
  q.first  <- Nil;
  q.last   <- Nil
(*@ clear q [l: int sequence]
    requires queue q l
    ensures  queue q empty *)

let clear_alt (q: queue) =
  q.length <- 0;
  q.first  <- Nil;
  q.last   <- Nil
(*@ clear_alt q
    requires q ~~> {length; first; last}
    ensures queue q empty *)

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
(*@ add x q [l: int sequence]
    requires queue q l
    ensures  queue q (l ++ (singleton x) ) *)


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
(*@ transfer q1 q2 [l1: int sequence] [l2: int sequence]
    requires queue q1 l1
    requires queue q2 l2
    ensures  queue q1 empty
    ensures  queue q2 (l2 ++ l1) *)
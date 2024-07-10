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
  { length = 0; first = Nil; last = Nil }
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

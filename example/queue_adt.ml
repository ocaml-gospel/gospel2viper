(*@ function end (s : int sequence)
: int =
  s[.. length s - 1] *)
(*@ requires s <> empty *)

(*@ function take_last
  (s : int sequence)
: int sequence =
  singleton (end s) *)
(*@ requires s <> empty *)

(*@ function drop_last
  (s : int sequence)
: int sequence =
  s[.. length s - 1] *)
(*@ requires s <> empty *)

type cell =
  | Nil
  | Cons of { mutable content : int;
              mutable next : cell }

(*@ predicate cellSeg
    (from: cell)
    (v: int sequence)
    (to: cell) =
  if v = empty then to = from
  else
    let Cons c = from in
    c ~~> {content; next} &&
    c.content = get v 0 &&
    cellSeg c.next (tl v) to *)

type queue = {
  mutable length : int;
  mutable first  : cell;
  mutable last   : cell
}

(*@ predicate queue
    (q: queue)
    (v: int sequence) =
  q ~~> {length; first; last} &&
  if v = empty then
    let Nil qlast = q.last in
    let Nil qfirst = q.first in
    q.length = 0
  else
    length v = q.length &&
    cellSeg q.first (drop_last v)
            q.last &&
    cellSeg q.last (take_last v)
            Nil *)

let create () : queue =
  let q : queue =
    Cons { length = 0;
           first  = Nil;
           last   = Nil } in
  (*@ fold queue q empty *)
  q
(*@ q = create ()
      ensures queue q empty *)

let clear (q: queue) =
  (*@ unfold queue q empty*)
  q.length <- 0;
  q.first  <- Nil;
  q.last   <- Nil;
  (*@ fold queue q empty *)
  ()
(*@ clear q
    requires q ~~> {length;
                    first;
                    last}
    ensures  queue q empty *)

let add (q: queue) (x: int) =
  let cell : cell =
    Cons { content = x;
           next = Nil} in
  (*@ apply queue_if q v *)
  if q.last = Nil then (
    q.length <- 1;
    q.first  <- cell;
    q.last   <- cell;
    (*@ fold cellSeg q.first empty
             q.last *)
    (*@ fold cellSeg Nil empty Nil *)
    (*@ fold cellSeg cell
             (singleton x) Nil *)
    ()
  ) else (
    q.length <- q.length + 1;
    (*@ unfold cellSeg q.last
               (take_last v) Nil *)
    q.last.next <- cell;
    (*@ fold cellSeg q.last.next
             empty cell *)
    (*@ fold cellSeg q.last
             (take_last v) cell *)
    (*@ fold cellSeg cell.next empty
             Nil *)
    (*@ fold cellSeg cell
             (singleton x) Nil *)
    (*@ apply CellSeg_trans q.first
              q.last cell
              (drop_last v)
              (take_last v)
              (singleton x) *)
    q.last <- cell;
  )
  (*@ fold queue q
           (v ++ (singleton x)) *)
(*@ add x q [v: int sequence]
    requires queue q v
    ensures  queue q (v ++
             (singleton x)) *)

let transfer (q: queue) (q1: queue) =
  (*@ apply queue_if_length q v *)
  if q.length > 0 then (
    (*@ apply queue_if q1 v1 *)
    if q1.last = Nil then (
      q1.length <- q.length;
      q1.first  <- q.first;
      q1.last   <- q.last;
      clear q;
      (*@ fold queue q1 v *)
      ()
    ) else (
      q1.length <-
        q1.length + q.length;
      (*@ unfold cellSeg q1.last
                 (take_last v1)
                 Nil *)
      q1.last.next <- q.first;
      (*@ fold cellSeg q1.last.next
               empty q.first *)
      (*@ fold cellSeg q1.last
               (take_last v1)
               q.first *)
      (*@ apply CellSeg_trans q1.last
                q.first q.last
                (take_last v1)
                (drop_last v)
                (take_last v) *)
      (*@ apply CellSeg_trans
                q1.first q1.last
                q.last (drop_last v1)
                ((take_last v1)
                  ++ (drop_last v))
                (take_last v) *)
      q1.last <- q.last;
      clear q;
      (*@ fold queue q1 (v1 ++ v) *)
      ()
    )
  ) else (
    (*@ fold queue q empty *)
    ()
  )
(*@ transfer q q1
            [v: int sequence]
            [v1: int sequence]
    requires queue q v && queue q1 v1
    ensures  queue q empty
    ensures  queue q1 (v1 ++ v) *)


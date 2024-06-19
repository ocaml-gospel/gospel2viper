(*@ open Sequence *)

type t
(*@ mutable model : int Sequence.t *)

val create : unit -> t
(*@ r = create ()
    produces r @ t
    ensures r = empty *)

val push : int -> t -> unit
(*@ push x l
    consumes l @ t
    produces l @ t
    ensures l = cons x (old l) *)

val pop : t -> int
(*@ x = pop l
    consumes l @ t
    produces l @ t
    ensures l = tl (old l) *)
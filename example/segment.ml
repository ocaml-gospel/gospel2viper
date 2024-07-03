type cell = {mutable elem: int; mutable next: cell}
(*@ mutable model view: int sequence *)

(*@ function nb_occ (values: int sequence) (e: int): int =
    let v = tl values in
    if values = empty then 0 else (
    if (hd values) = 0
    then (1 + (nb_occ v e))
    else       nb_occ v e)
*)

(*@ function contains_once (values: int sequence) (e: int): bool =
    (nb_occ values e) = 1 *)

(*@ function contains_zero (values: int sequence) (e: int): bool =
    (nb_occ values e) = 0 *)

(*@ predicate lseg (first: cell) (last: cell) (view: int sequence) =
  first <> last ->
    first ~~> {next; elem} &&
    0 < length view &&
    contains_once view first.elem &&
    first.elem = get view 0 &&
    let v = tl view in
    lseg first.next last v *)

(*@ function contains (first: cell) (last: cell) (values: int sequence) (e: int): bool =
    if first = last then false else (
      if first.elem = e then true else (
        let v = tl values in
        contains first.next last v e
      )
    )
*)
(*@ requires lseg first last values *)

type t = { mutable value : int;
           mutable next : t }
(*@ mutable model view : integer sequence *)

(*@ predicate lseg (first: t) (last: t) (l: integer sequence) =
      first <> last ->
        first ~~> {value; next} && length l > 0 &&
        let ll = tl l in
        lseg first.next last ll *)

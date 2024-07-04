type tuple = {mutable fst: int; mutable snd: int}
(*@ mutable model view_fst: int
    mutable model view_snd: int *)

(*@ predicate tuple_repr (t: tuple) (view_fst: int) (view_snd: int) =
    t ~~> {fst; snd} &&
    view_fst = t.fst && view_snd = t.snd && t.fst >= 0 *)
function end (s: Seq[Int]) : Int
  requires s != Seq[Int]()
{ s[|s| - 1] }

function take_last (s: Seq[Int])
: Seq[Int]
  requires s != Seq[Int]()
{ Seq(end(s)) }

function drop_last (s: Seq[Int])
: Seq[Int]
  requires s != Seq[Int]()
{ s[.. |s| - 1] }

adt Cell {
  Nil()
  Cons(cell: Ref)
}

field content : Int
field next: Cell

predicate CellSeg (from: Cell,
                   v: Seq[Int],
                   to: Cell)
{
  v == Seq[Int]() ?
    to == from
  : from.isCons &&
    let c == (from.cell) in
    acc(c.content) &&
    acc(c.next) &&
    c.content == v[0] &&
    CellSeg(c.next, v[1 ..], to)
}

field length: Int
field first: Cell
field last: Cell

predicate Queue (q: Ref, v: Seq[Int])
{
  acc(q.length) && acc(q.first) &&
  acc(q.last) &&
  (v == Seq[Int]()
   ? q.last == Nil() &&
     let qlast == (q.last.cell) in
     q.first.isNil &&
     let qfirst == (q.first.cell) in
     q.length == 0
   : |v| == q.length &&
     CellSeg(q.first, drop_last(v),
             q.last) &&
     CellSeg(q.last, take_last(v),
             Nil()))
}

method CellSeg_trans (
  c: Cell, c1: Cell, c2: Cell,
  v: Seq[Int], v1: Seq[Int],
  v2: Seq[Int])
  requires CellSeg(c, v, c1) &&
           CellSeg(c1, v1, c2) &&
           CellSeg(c2, v2, Nil())
  ensures  CellSeg(c, v ++ v1, c2) &&
           CellSeg(c2, v2, Nil())
{
  unfold CellSeg(c, v, c1)
  if (v == Seq[Int]()) {
  }
  else {
    CellSeg_trans(c.cell.next, c1,
                  c2, v[1 ..], v1, v2
                 )
    fold CellSeg(c, v ++ v1, c2)
  }
}

method create () returns (q: Ref)
  ensures Queue(q, Seq[Int]())
{
  q := new(length, first, last)
  q.length := 0
  q.first := Nil();
  q.last := Nil();
  fold Queue(q, Seq[Int]())
}


method clear (q: Ref)
  requires acc(q.length) &&
           acc(q.first)  &&
           acc(q.last)
  ensures Queue(q, Seq[Int]())
{
  q.length := 0
  q.first := Nil()
  q.last := Nil()
  fold Queue(q, Seq[Int]())
}

method queue_if (q: Ref, L: Seq[Int])
  requires Queue(q, L)
  ensures acc(q.length) &&
          acc(q.first)  &&
          acc(q.last)   &&
          (q.last == Nil()
          ? L == Seq[Int]() &&
            q.first  == Nil() &&
            q.length == 0
          : |L| > 0 &&
            q.length == |L| &&
            CellSeg(q.first,
              drop_last(L),
              q.last) &&
            CellSeg(q.last,
                    Seq(end(L)),
                    Nil()))
{
  unfold Queue(q, L)
  if (L != Seq[Int]() &&
      q.last == Nil())
  { unfold CellSeg(q.last,
      Seq(end(L)), Nil()) }
}

method queue_if_length (q: Ref,
  L: Seq[Int])
  requires Queue(q, L)
  ensures  acc(q.length) &&
           acc(q.first)  &&
           acc(q.last)   &&
           (q.length > 0
            ? |L| > 0 &&
              q.length == |L| &&
              CellSeg(q.first,
                      drop_last(L),
                      q.last) &&
              CellSeg(q.last,
                      Seq(end(L)),
                      Nil())
            : q.length == 0 &&
              L == Seq[Int]() &&
              q.first == Nil() &&
              q.last == Nil())
{
  unfold Queue(q, L)
}

method add (q: Ref, x: Int,
  v: Seq[Int])
  requires Queue(q, v)
  ensures Queue(q, v ++ Seq(x))
{
  var c : Ref := new(content, next)
  c.content := x
  c.next := Nil()
  var cell : Cell := Cons(c)
  queue_if(q, v)
  if (q.last == Nil()) {
    q.length := 1
    q.first  := cell
    q.last   := cell
    fold CellSeg(q.first, Seq[Int](),
                 q.last)
    fold CellSeg(Nil(), Seq[Int](),
                 Nil())
    fold CellSeg(cell, Seq(x), Nil())
  }
  else {
    // q.first --> q.last --> Nil()
    // cell --> Nil()
    q.length := q.length + 1
    unfold CellSeg(q.last,
                   take_last(v),
                   Nil())
    // q.last --> cell --> Nil()
    // q.first --> q.last --> cell --> Nil()
    q.last.cell.next := cell
    fold CellSeg(q.last.cell.next,
                 Seq[Int](), cell)
    fold CellSeg(q.last,
                 take_last(v), cell)
    fold CellSeg(cell.cell.next,
                 Seq[Int](), Nil())
    fold CellSeg(cell, Seq(x), Nil())
    CellSeg_trans(q.first, q.last,
                  cell, drop_last(v),
                  take_last(v),
                  Seq(x))
    // q.first --> q.last --> tmp
    q.last := cell
  }
  fold Queue(q, v ++ Seq(x))
}

method transfer (q: Ref, q1: Ref,
  v: Seq[Int], v1: Seq[Int])
  requires Queue(q, v) &&
           Queue(q1, v1)
  ensures  Queue(q, Seq[Int]())
  ensures  Queue(q1, v1 ++ v)
{
  queue_if_length(q, v)
  if (q.length > 0) {
    queue_if(q1, v1)
    if (q1.last.isNil) {
      // [q1] is the empty queue
      q1.length := q.length
      q1.first  := q.first
      q1.last   := q.last
      clear(q)
      fold Queue(q1, v)
    }
    else {
      // [q1] is not the empty queue
      q1.length := q1.length +
                    q.length
      unfold CellSeg(q1.last,
                     take_last(v1),
                     Nil())
      q1.last.cell.next := q.first
      fold CellSeg(q1.last.cell.next,
                   Seq[Int](),
                   q.first)
      fold CellSeg(q1.last,
                   take_last(v1),
                   q.first)
      CellSeg_trans(q1.last, q.first,
                    q.last,
                    take_last(v1),
                    drop_last(v),
                    take_last(v))
      // q1.last --> q.first --> q.last
      CellSeg_trans(q1.first,
                    q1.last, q.last,
                    drop_last(v1),
                    take_last(v1) ++
                      drop_last(v),
                    take_last(v))
      q1.last := q.last
      // q1.first --> q1.last --> q.last --> Nil
      clear(q)
      fold Queue(q1, v1 ++ v)
    }
  }
  else {
    // [q] is the empty queue
    fold Queue(q, Seq[Int]())
  }
}

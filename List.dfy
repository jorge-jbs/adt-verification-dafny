class NonEmpty<A> {
  ghost var repr: set<object>;
  var data: A;
  var next: NonEmpty?<A>;

  predicate Valid()
    reads this, repr
  {
    this in repr
    && ( next != null ==>
          next in repr
          && repr == {this} + next.repr
          && this !in next.repr
          && next.Valid()
      )
    && ( next == null ==>
          repr == {this}
      )
  }

  predicate ValidUntil(n: NonEmpty<A>)
    reads this, repr
  {
    this in repr
    && n in repr
    && ( if this == n || next == n then
          true
        else if next != null then
          next in repr
          && repr == {this} + next.repr
          && this !in next.repr
          && next.ValidUntil(n)
        else
          repr == {this}
      )
  }

  constructor Init(d: A)
    ensures Valid()
    ensures fresh(repr - {this})
    ensures data == d
    ensures next == null
  {
    repr := {this};
    data := d;
    next := null;
  }

  predicate IsPrevOf(n: NonEmpty<A>)
    reads this
  {
    next == n
  }

  predicate IsBefore(n: NonEmpty<A>)
    reads this
  {
    n in repr
  }
}

type List<A> = NonEmpty?<A>

function Repr<A>(xs: List<A>): set<object>
  reads xs
{
  if xs == null then
    {}
  else
    xs.repr
}

predicate Valid<A>(xs: List<A>)
  reads xs, Repr(xs)
{
  xs != null ==> xs.Valid()
}

function Model<A>(node: List<A>): seq<A>
  reads node, Repr(node)
  decreases Repr(node)
  requires Valid(node)
{
  if node == null then
    []
  else
    assert node.Valid();
    assert node.next != null ==> node.next.Valid();
    [node.data] + Model(node.next)
}

function method Head<A>(xs: NonEmpty<A>): A
  reads xs, xs.repr
  requires xs.Valid()
  ensures Head(xs) == Model(xs)[0]
{
  xs.data
}

function method Tail<A>(xs: NonEmpty<A>): List<A>
  reads xs, xs.repr
  requires xs.Valid()
  ensures Valid(Tail(xs))
  ensures Model(Tail(xs)) == Model(xs)[1..]
  ensures Repr(Tail(xs)) <= Repr(xs) - {xs}
{
  xs.next
}

method Cons<A>(x: A, xs: List<A>) returns (res: NonEmpty<A>)
  requires xs != null ==> xs.Valid()
  ensures res.Valid()
  ensures Model(res) == [x] + Model(xs)
  ensures fresh(Repr(res) - Repr(xs))
  ensures Repr(res) >= Repr(xs)
{
  res := new NonEmpty.Init(x);
  res.next := xs;
  if res.next != null {
    res.repr := {res} + res.next.repr;
  }
}

method Append<A>(xs: List<A>, ys: List<A>) returns (res: List<A>)
  decreases Repr(xs)
  requires Valid(xs)
  requires Valid(ys)
  ensures Valid(res)
  ensures Model(res) == Model(xs) + Model(ys)
{
  if xs == null {
    res := ys;
  } else {
    res := Append(Tail(xs), ys);
    res := Cons(Head(xs), res);
  }
}

function rev<A>(xs: seq<A>): seq<A>
{
  if |xs| == 0 then
    []
  else
    rev(xs[1..]) + [xs[0]]
}

method reverseAux<A>(xs: NonEmpty<A>, ys: List<A>) returns (xs_: List<A>, ys_: NonEmpty<A>)
  modifies xs, xs.repr

  requires Valid(xs) && Valid(ys)
  ensures Valid(xs_) && Valid(ys_)

  requires Repr(xs) !! Repr(ys)
  ensures Repr(xs_) !! Repr(ys_)

  ensures old(Repr(xs)) + old(Repr(ys)) == Repr(xs_) + Repr(ys_)
  ensures old(Repr(xs)) > Repr(xs_)
  ensures rev(old(Model(xs))) + old(Model(ys)) == rev(Model(xs_)) + Model(ys_)
{
  xs_ := Tail(xs);
  ys_ := xs;
  ys_.next := ys;
  ys_.repr := Repr(ys) + {ys_};
}

method reverse<A>(xs: List<A>) returns (res: List<A>)
  modifies xs, Repr(xs)
  requires Valid(xs)
  ensures Valid(res)
  ensures old(Repr(xs)) == Repr(res)
  ensures rev(old(Model(xs))) == Model(res)
{
  var aux := xs;
  res := null;
  while aux != null
    decreases Repr(aux)
    invariant Repr(aux) !! Repr(res)
    invariant Valid(aux)
    invariant Valid(res)
    invariant old(Repr(xs)) == Repr(aux) + Repr(res)
    invariant rev(old(Model(xs))) == rev(Model(aux)) + Model(res)
  {
    aux, res := reverseAux(aux, res);
  }
}

function method PrevNode<A>(head: NonEmpty<A>, mid: NonEmpty<A>):
    (prev: NonEmpty<A>)
  decreases Repr(head)
  reads head, head.repr, mid, mid.repr
  requires mid in head.repr
  requires head.ValidUntil(mid)
  requires head != mid
  ensures prev.next == mid
  ensures head.ValidUntil(prev)
{
  if head.next == mid then
    head
  else
    PrevNode(head.next, mid)
}

lemma ValidUntilFromValid<A>(head: NonEmpty<A>, mid: NonEmpty<A>)
  decreases Repr(head)
  requires mid in head.repr
  requires head.Valid()
  ensures head.ValidUntil(mid) && mid.Valid()
{
  if head == mid {
    assert mid.Valid();
  } else if head.next != null {
    ValidUntilFromValid(head.next, mid);
    assert mid.Valid();
  } else {
    assert mid.Valid();
  }
}

ghost method Repair(prevs: seq<NonEmpty<int>>, mid: List<int>)
  modifies set n | n in multiset(prevs) :: n`repr
  requires mid !in multiset(prevs)
  requires forall n | n in prevs :: n !in Repr(mid)
  requires forall i, j | 0 <= i < j < |prevs| :: prevs[i] != prevs[j]
  requires forall i | 0 <= i < |prevs|-1 :: prevs[i].next == prevs[i+1]
  requires prevs != [] ==> prevs[|prevs|-1].next == mid
  requires Valid(mid)
  ensures Valid(mid)
  // ensures prevs != [] ==> prevs[0].Valid()
  ensures forall n | n in multiset(prevs) :: n.Valid()
{
  if prevs != [] {
    var prev := prevs[|prevs|-1];
    assert prev in multiset(prevs);
    assert Valid(mid);
    prev.repr := {prev} + Repr(mid);
    assert prev.Valid();
    assert prevs == prevs[..|prevs|-1] + prevs[|prevs|-1..|prevs|];
    assert multiset(prevs[..|prevs|-1]) <= multiset(prevs);
    Repair(prevs[..|prevs|-1], prev);
  }
}

lemma IsBeforeStepRight<A>(a: NonEmpty<A>, b: NonEmpty<A>)
  decreases a.repr
  requires Valid(a)
  requires Valid(b)
  requires a != b
  requires b.next != null
  requires a.IsBefore(b)
  ensures a.IsBefore(b.next)
{
  if a.next != b {
    IsBeforeStepRight(a.next, b);
  }
}

lemma IsBeforeSubset<A>(a: NonEmpty<A>, b: NonEmpty<A>)
  decreases a.repr
  requires Valid(a)
  requires Valid(b)
  requires a.IsBefore(b)
  ensures a.repr >= b.repr
{
  if a != b {
    IsBeforeSubset(a.next, b);
  }
}

lemma IsBeforeAntisym<A>(a: NonEmpty<A>, b: NonEmpty<A>)
  decreases Repr(a)
  requires Valid(a)
  requires Valid(b)
  requires a.IsBefore(b)
  requires b.IsBefore(a)
  ensures a == b
{
  if a != b && a.next != null {
    IsBeforeStepRight(b, a);
    IsBeforeAntisym(a.next, b);
  }
}

function TakeSeq<A>(head: List<A>, mid: List<A>): (res: seq<NonEmpty<A>>)
  decreases Repr(head)
  reads Repr(head)
  reads Repr(mid)
  requires Valid(head)
  requires Valid(mid)
  requires mid in Repr(head)
  ensures res != [] ==> res[0] == head && res[|res|-1].next == mid
  ensures forall n | n in res :: n in Repr(head)
  ensures forall i | 0 <= i < |res|-1 :: res[i].next == res[i+1]
  ensures mid !in multiset(res)
  ensures forall n | n in multiset(res) :: n !in Repr(mid)
  ensures forall i, j | 0 <= i < j < |res| :: res[i] != res[j]
  ensures forall i | 0 <= i < |res|-1 :: res[i].next == res[i+1]
  ensures res != [] ==> res[|res|-1].next == mid
  ensures mid !in res
{
  if head == mid then
    []
  else
    assume head in Repr(mid);
    IsBeforeAntisym(head, mid);
    assert head !in Repr(mid);
    [head] + TakeSeq(head.next, mid)
}

method InPlaceInsert(head: NonEmpty<int>, mid: NonEmpty<int>, x: int)
  modifies head, head.repr, mid, mid.repr
  requires head != mid
  requires head.Valid() && mid.Valid()
  requires mid in head.repr
  ensures head.Valid() && mid.Valid()
{
  ghost var prevs := TakeSeq(head, mid);
  assert forall i | 0 <= i < |prevs|-1 :: prevs[i].next == prevs[i+1];
  assert prevs != [] ==> prevs[|prevs|-1].next == mid;
  var n := new NonEmpty.Init(x);
  assert forall i | 0 <= i < |prevs|-1 :: prevs[i].next == prevs[i+1];
  assert prevs != [] ==> prevs[|prevs|-1].next == mid;
  n.next := mid.next;
  n.repr := Repr(mid.next) + {n};
  mid.next := n;
  mid.repr := {n} + mid.repr;
  Repair(prevs, mid);
  assert Valid(head);
  assert Valid(mid);
}

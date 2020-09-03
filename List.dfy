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
    ensures Valid() && fresh(repr - {this})
    ensures data == d
    ensures next == null
  {
    repr := {this};
    data := d;
    next := null;
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

  ensures old(Repr(xs)) + old(Repr(ys)) >= Repr(xs_) + Repr(ys_)
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
  ensures old(Repr(xs)) >= Repr(res)
  ensures rev(old(Model(xs))) == Model(res)
{
  var aux := xs;
  res := null;
  while aux != null
    decreases Repr(aux)
    invariant Repr(aux) !! Repr(res)
    invariant Valid(aux)
    invariant Valid(res)
    invariant old(Repr(xs)) >= Repr(aux) + Repr(res)
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

/*
method InPlaceInsert<A>(head: NonEmpty<A>, mid: NonEmpty<A>, x: A)
  modifies head, head.repr, mid, mid.repr
  requires head != mid
  requires head.Valid() && mid.Valid()
  requires mid in head.repr
  ensures head.Valid() && mid.Valid()
{
  ValidUntilFromValid(head, mid);
  var prev := PrevNode(head, mid);
  assert head.ValidUntil(prev);
  assert head.ValidUntil(mid);
  var n := new NonEmpty.Init(x);
  n.next := mid.next;
  n.repr := Repr(mid.next) + {n};
  assert head.ValidUntil(prev);
  assert head.ValidUntil(mid);
  assert n.Valid();
  mid.next := n;
  assert head.ValidUntil(prev);
  assert head.ValidUntil(mid);
  mid.repr := mid.repr + {n};
  assert head.ValidUntil(prev);
  assert head.ValidUntil(mid);
  assert mid.Valid();
  var current := mid;
  assert head.ValidUntil(prev);
  assert head.ValidUntil(mid);
  /*
  while current != head
    invariant current.Valid()
    //invariant head.ValidUntil(current)
  {
    current := PrevNode(head, current);
  }
     */
}
*/

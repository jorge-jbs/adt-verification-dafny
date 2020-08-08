class NonEmpty<A> {
  ghost var repr: set<object>;
  var data: A;
  var next: NonEmpty?<A>;

  function Valid(): bool
    reads this, repr
  {
    this in repr
    && ( next != null ==>
          next in repr
          && next.repr <= repr
          && this !in next.repr
          && next.Valid()
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

/*
function Model<A>(node: NonEmpty<A>): seq<A>
  reads node, node.repr
  requires node.Valid()
{
  [node.data] + (if node.next == null then [] else Model(node.next))
}
*/

function Model<A>(node: List<A>): seq<A>
  reads node, (if node == null then {} else node.repr)
  decreases (if node == null then {} else node.repr)
  requires node != null ==> node.Valid()
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

function method Tail<A>(xs: NonEmpty<A>): (t: List<A>)
  reads xs, xs.repr
  requires xs.Valid()
  ensures Tail(xs) != null ==> Tail(xs).Valid()
  ensures Model(Tail(xs)) == Model(xs)[1..]
{
  xs.next
}

method Cons<A>(x: A, xs: List<A>) returns (res: NonEmpty<A>)
  requires xs != null ==> xs.Valid()
  ensures res.Valid()
  ensures Model(res) == [x] + Model(xs)
{
  res := new NonEmpty.Init(x);
  res.next := xs;
  if res.next != null {
    res.repr := {res} + res.next.repr;
  }
}

method Append<A>(xs: List<A>, ys: List<A>) returns (res : List<A>)
  decreases (if xs == null then {} else xs.repr)
  requires xs != null ==> xs.Valid()
  requires ys != null ==> ys.Valid()
  ensures res != null ==> res.Valid()
  ensures Model(res) == Model(xs) + Model(ys)
{
  if xs == null {
    res := ys;
  } else {
    res := Append(Tail(xs), ys);
    res := Cons(Head(xs), res);
  }
}

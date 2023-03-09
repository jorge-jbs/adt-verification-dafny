include "../src/Utils.dfy"

class Node<A> {
  ghost var repr: set<object>;
  var data: A;
  var next: Node?<A>;

  ghost predicate Valid()
    reads this, repr
  {
    && this in repr
    && (if next == null then
        repr == {this}
      else
        && next in repr
        && repr == {this} + next.repr
        && this !in next.repr
        && next.Valid()
      )
  }

  ghost predicate ValidUntil(n: Node<A>)
    reads this, repr
  {
    && this in repr
    && n in repr
    && ( if this == n || next == n then
          true
        else if next != null then
          && next in repr
          && repr == {this} + next.repr
          && this !in next.repr
          && next.ValidUntil(n)
        else
          repr == {this}
      )
  }

  ghost function Model(): seq<A>
    decreases repr
    reads this, repr
    requires Valid()
  {
    if next == null then
      [data]
    else
      [data] + next.Model()
  }

  constructor(d: A)
    ensures Valid()
    ensures forall x | x in repr - {this} :: fresh(x)
    ensures Model() == [d]
    ensures data == d
    ensures next == null
  {
    repr := {this};
    data := d;
    next := null;
  }

  ghost predicate IsPrevOf(n: Node<A>)
    reads this
  {
    next == n
  }

  ghost predicate IsBefore(n: Node<A>)
    reads this
  {
    n in repr
  }
}

ghost function ReprAux<A>(node: Node?<A>): set<object>
  reads node
{
  if node == null then
    {}
  else
    node.repr
}

ghost predicate ValidAux<A>(node: Node?<A>)
  reads node, ReprAux(node)
{
  node != null ==> node.Valid()
}

class SinglyLinkedListWithRecursion<A> {
  var head: Node?<A>

  ghost function Repr(): set<object>
    reads this, head
  {
    if head == null then
      {}
    else
      head.repr
  }

  ghost predicate Valid()
    reads this, head, Repr()
  {
    head != null ==> head.Valid()
  }

  ghost function Model(): seq<A>
    reads this, head, Repr()
    requires Valid()
  {
    if head == null then
      []
    else
      head.Model()
  }

  method Top() returns (x: A)
    requires Valid()
    requires Model() != []
    ensures x == Model()[0]
  {
    x := head.data;
  }

  /*
  function Tail(): List
    reads xs, xs.repr
    requires xs.Valid()
    ensures Valid(Tail(xs))
    ensures Model(Tail(xs)) == Model(xs)[1..]
    ensures Repr(Tail(xs)) <= Repr(xs) - {xs}
  {
    xs.next
  }
  */

  /*
  method Cons(x: A, xs: List) returns (res: Node<A>)
    requires xs != null ==> xs.Valid()
    ensures res.Valid()
    ensures Model(res) == [x] + Model(xs)
    ensures fresh(Repr(res) - Repr(xs))
    ensures Repr(res) >= Repr(xs)
  {
    res := new Node(x);
    res.next := xs;
    if res.next != null {
      res.repr := {res} + res.next.repr;
    }
  }

  method Append(xs: List, ys: List) returns (res: List)
    decreases Repr(xs)
    requires Valid(xs)
    requires Valid(ys)
    ensures Valid(res)
    ensures Model(res) == Model(xs) + Model(ys)
  {
    if xs == null {
      res := ys;
    } else {
      res := Append(xs.next, ys);
      res := Cons(xs.data, res);
    }
  }

  method ReverseAux(xs: Node<A>, ys: List)
    returns (xs_: List, ys_: Node<A>)
    modifies xs, xs.repr

    requires Valid(xs) && Valid(ys)
    ensures Valid(xs_) && Valid(ys_)

    requires Repr(xs) !! Repr(ys)
    ensures Repr(xs_) !! Repr(ys_)

    ensures old(Repr(xs)) + old(Repr(ys)) == Repr(xs_) + Repr(ys_)
    ensures old(Repr(xs)) > Repr(xs_)
    ensures Seq.Rev(old(Model(xs))) + old(Model(ys)) == Seq.Rev(Model(xs_)) + Model(ys_)
  {
    xs_ := xs.next;
    ys_ := xs;
    ys_.next := ys;
    ys_.repr := Repr(ys) + {ys_};
  }

  method Reverse(xs: List) returns (res: List)
    modifies xs, Repr(xs)
    requires Valid(xs)
    ensures Valid(res)
    ensures old(Repr(xs)) == Repr(res)
    ensures Seq.Rev(old(Model(xs))) == Model(res)
  {
    var aux := xs;
    res := null;
    while aux != null
      decreases Repr(aux)
      invariant Repr(aux) !! Repr(res)
      invariant Valid(aux)
      invariant Valid(res)
      invariant old(Repr(xs)) == Repr(aux) + Repr(res)
      invariant Seq.Rev(old(Model(xs))) == Seq.Rev(Model(aux)) + Model(res)
    {
      aux, res := ReverseAux(aux, res);
    }
  }
  */

  static function PrevNode(head: Node<A>, mid: Node<A>): (prev: Node<A>)
    decreases head.repr
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

  static lemma ValidUntilFromValid(head: Node<A>, mid: Node<A>)
    decreases head.repr
    requires mid in head.repr
    requires head.Valid()
    ensures head.ValidUntil(mid) && mid.Valid()
  {
    if head != mid && head.next != null {
      ValidUntilFromValid(head.next, mid);
    }
  }

  ghost method Repair(prevs: seq<Node<A>>, mid: Node?<A>)
    modifies set n | n in multiset(prevs) :: n`repr
    requires mid !in multiset(prevs)
    requires forall n | n in prevs :: n !in ReprAux(mid)
    requires forall i, j | 0 <= i < j < |prevs| :: prevs[i] != prevs[j]
    requires forall i | 0 <= i < |prevs|-1 :: prevs[i].next == prevs[i+1]
    requires prevs != [] ==> prevs[|prevs|-1].next == mid
    requires ValidAux(mid)
    ensures ValidAux(mid)
    ensures forall n | n in multiset(prevs) :: n.Valid()
    // ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
  {
    if prevs != [] {
      var prev := prevs[|prevs|-1];
      assert prev in multiset(prevs);
      prev.repr := {prev} + ReprAux(mid);
      assert prevs == prevs[..|prevs|-1] + prevs[|prevs|-1..|prevs|];
      assert multiset(prevs[..|prevs|-1]) <= multiset(prevs);
      Repair(prevs[..|prevs|-1], prev);
    }
  }

  static lemma IsBeforeStepRight(a: Node<A>, b: Node<A>)
    decreases a.repr
    requires ValidAux(a)
    requires ValidAux(b)
    requires b.next != null
    requires a.IsBefore(b)
    ensures a.IsBefore(b.next)
  {
    if a != b && a.next != b {
      IsBeforeStepRight(a.next, b);
    }
  }

  static lemma IsBeforeSubset(a: Node<A>, b: Node<A>)
    decreases a.repr
    requires ValidAux(a)
    requires ValidAux(b)
    requires a.IsBefore(b)
    ensures a.repr >= b.repr
  {
    if a != b {
      IsBeforeSubset(a.next, b);
    }
  }

  static lemma IsBeforeAntisym(a: Node<A>, b: Node<A>)
    decreases ReprAux(a)
    requires ValidAux(a)
    requires ValidAux(b)
    requires a.IsBefore(b)
    requires b.IsBefore(a)
    ensures a == b
  {
    if a != b && a.next != null {
      IsBeforeStepRight(b, a);
      IsBeforeAntisym(a.next, b);
    }
  }

  static ghost function TakeSeq(head: Node<A>, mid: Node<A>): (res: seq<Node<A>>)
    decreases ReprAux(head)
    reads ReprAux(head)
    reads ReprAux(mid)
    requires ValidAux(head)
    requires ValidAux(mid)
    requires mid in ReprAux(head)
    ensures head != mid ==> head in res
    ensures res != [] ==> res[0] == head && res[|res|-1].IsPrevOf(mid)
    ensures forall n | n in res :: n in ReprAux(head)
    ensures mid !in res
    ensures forall n | n in multiset(res) :: n !in ReprAux(mid)
    ensures forall i, j | 0 <= i < j < |res| :: res[i] != res[j]
    ensures forall i | 0 <= i < |res|-1 :: res[i].IsPrevOf(res[i+1])
    ensures res != [] ==> res[|res|-1].IsPrevOf(mid)
  {
    if head == mid then
      []
    else
      if head in ReprAux(mid) then
        IsBeforeAntisym(head, mid);
        assert head !in ReprAux(mid);
        assert false;
        []
      else
        assert head !in ReprAux(mid);
        var res := [head] + TakeSeq(head.next, mid);
        assert res != [] ==> res[0] == head && res[|res|-1].IsPrevOf(mid);
        res
  }

  method Insert(mid: Node<A>, x: A)
    modifies Repr()
    requires Valid()
    requires mid.Valid()
    requires mid in Repr()
    ensures Valid()
    ensures mid.Valid()
    ensures fresh(mid.next)
    // ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    // ensures Model() == Seq.Insert(x, old(Model()), old(GetIndex(mid))+1)
  {
    var n := new Node(x);
    ghost var prevs := TakeSeq(head, mid);
    assert forall i | 0 <= i < |prevs|-1 :: prevs[i].IsPrevOf(prevs[i+1]);
    assert prevs != [] ==> prevs[|prevs|-1].IsPrevOf(mid);
    n.next := mid.next;
    /*GHOST*/ n.repr := ReprAux(mid.next) + {n};
    mid.next := n;
    /*GHOST*/ mid.repr := {n} + mid.repr;
    /*GHOST*/ Repair(prevs, mid);
  }
}

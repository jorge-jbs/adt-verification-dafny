include "../../../src/Utils.dfy"

class Node {
  ghost var repr: set<object>;
  var data: int;
  var next: Node?;

  predicate Valid()
    reads this, repr
  {
    && this in repr
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

  predicate ValidUntil(n: Node)
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

  constructor(d: int)
    ensures Valid()
    ensures fresh(repr - {this})
    ensures data == d
    ensures next == null
  {
    repr := {this};
    data := d;
    next := null;
  }

  predicate IsPrevOf(n: Node)
    reads this
  {
    next == n
  }

  predicate IsBefore(n: Node)
    reads this
  {
    n in repr
  }
}

function ReprAux(node: Node?): set<object>
  reads node
{
  if node == null then
    {}
  else
    node.repr
}

predicate ValidAux(node: Node?)
  reads node, ReprAux(node)
{
  node != null ==> node.Valid()
}

class SinglyLinkedListWithRecursion {
  var head: Node?

  function Repr(): set<object>
    reads this, head
  {
    if head == null then
      {}
    else
      head.repr
  }

  predicate Valid()
    reads this, head, Repr()
  {
    head != null ==> head.Valid()
  }

  static function ModelAux(node: Node?): seq<int>
    reads node, ReprAux(node)
    decreases ReprAux(node)
    requires ValidAux(node)
  {
    if node == null then
      []
    else
      assert ValidAux(node);
      assert node.next != null ==> node.next.Valid();
      [node.data] + ModelAux(node.next)
  }

  function Model(): seq<int>
    reads this, head, Repr()
    requires Valid()
  {
    ModelAux(head)
  }

  method Top() returns (x: int)
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
  method Cons(x: A, xs: List) returns (res: Node)
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

  method ReverseAux(xs: Node, ys: List)
    returns (xs_: List, ys_: Node)
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

  static function PrevNode(head: Node, mid: Node): (prev: Node)
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

  static lemma ValidUntilFromValid(head: Node, mid: Node)
    decreases head.repr
    requires mid in head.repr
    requires head.Valid()
    ensures head.ValidUntil(mid) && mid.Valid()
  {
    if head != mid && head.next != null {
      ValidUntilFromValid(head.next, mid);
    }
  }

  ghost method Repair(prevs: seq<Node>, mid: Node?)
    modifies set n | n in multiset(prevs) :: n`repr
    requires mid !in multiset(prevs)
    requires forall n | n in prevs :: n !in ReprAux(mid)
    requires forall i, j | 0 <= i < j < |prevs| :: prevs[i] != prevs[j]
    requires forall i | 0 <= i < |prevs|-1 :: prevs[i].next == prevs[i+1]
    requires prevs != [] ==> prevs[|prevs|-1].next == mid
    requires ValidAux(mid)
    ensures ValidAux(mid)
    ensures forall n | n in multiset(prevs) :: n.Valid()
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

  lemma IsBeforeStepRight(a: Node, b: Node)
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

  lemma IsBeforeSubset(a: Node, b: Node)
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

  lemma IsBeforeAntisym(a: Node, b: Node)
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

  function TakeSeq(head: Node, mid: Node): (res: seq<Node>)
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

  method Insert(head: Node, mid: Node, x: int)
    modifies head, head.repr, mid, mid.repr
    requires head != mid
    requires head.Valid() && mid.Valid()
    requires mid in head.repr
    ensures head.Valid() && mid.Valid()
  {
    var n := new Node(x);
    ghost var prevs := TakeSeq(head, mid);
    assert forall i | 0 <= i < |prevs|-1 :: prevs[i].IsPrevOf(prevs[i+1]);
    assert prevs != [] ==> prevs[|prevs|-1].IsPrevOf(mid);
    n.next := mid.next;
    n.repr := ReprAux(mid.next) + {n};
    mid.next := n;
    mid.repr := {n} + mid.repr;
    /*GHOST*/ Repair(prevs, mid);
    assert ValidAux(head);
    assert ValidAux(mid);
  }
}

include "../../../src/Utils.dfy"

class Node<A> {
  var prev: Node?<A>;
  var data: A;
  var next: Node?<A>;

  constructor(prev: Node?<A>, data: A, next: Node?<A>)
    ensures this.prev == prev
    ensures this.data == data
    ensures this.next == next
  {
    this.prev := prev;
    this.data := data;
    this.next := next;
  }

  predicate IsPrevOf(n: Node<A>)
    reads this
  {
    next == n
  }

  predicate IsNextOf(n: Node<A>)
    reads this
  {
    prev == n
  }
}

class List<A> {
  var head: Node?<A>;
  ghost var spine: seq<Node<A>>;

  function Repr(): set<object>
    reads this
  {
    set x | x in spine
  }

  predicate Valid()
    reads this, Repr()
  {
    && (forall i | 0 <= i < |spine|-1 ::
      // spine[i].IsPrevOf(spine[i+1]) && spine[i+1].IsNextOf(spine[i])
      spine[i].next == spine[i+1] && spine[i+1].prev == spine[i]
    )
    && (if head == null then
      spine == []
    else
      && spine != []
      && spine[0] == head
      && spine[0].prev == null
      && spine[|spine|-1].next == null
    )
  }

  lemma DistinctSpineAux(n: nat)
    decreases |spine| - n
    requires Valid()
    requires 0 <= n <= |spine|
    ensures forall i, j | n <= i < j < |spine| :: spine[i] != spine[j]
  {
    if n == |spine| {
      assert spine[n..] == [];
    } else {
      DistinctSpineAux(n+1);
      assert forall i, j | n+1 <= i < j < |spine| :: spine[i] != spine[j];
      if spine[n] in spine[n+1..] {
        assert spine[n].next == spine[n+1];
        var i: nat :| n + 1 <= i < |spine| && spine[i] == spine[n];
        assert spine[n].next == spine[i].next == spine[i+1];
        assert n + 1 < i + 1;
        assert spine[i+1] != spine[n+1] && spine[i+1] == spine[n+1];
        assert false;
      }
      assert spine[n] !in spine[n+1..];
      assert forall i, j | n <= i < j < |spine| :: spine[i] != spine[j];
    }
  }

  lemma DistinctSpine()
    requires Valid()
    ensures forall i, j | 0 <= i < j < |spine| :: spine[i] != spine[j]
  {
    DistinctSpineAux(0);
  }

  static function ModelAux(xs: seq<Node<A>>): seq<A>
    reads set x | x in xs :: x`data
  {
    if xs == [] then
      []
    else
      assert xs[0] in xs;
      assert forall x | x in xs[1..] :: x in xs;
      [xs[0].data] + ModelAux(xs[1..])
  }

  lemma HeadNextNullImpliesSingleton()
    requires Valid()
    requires head != null
    requires head.next == null
    ensures spine == [head]
  {
    if |spine| != 1 {
      assert |spine| >= 2;
      assert spine[0].next == spine[1];
      assert false;
    } else {
      assert spine == [head];
    }
  }

  function Model(): seq<A>
    reads this, spine
    requires Valid()
  {
    ModelAux(spine)
  }

  static lemma ModelRelationWithSpineAux(spine: seq<Node<A>>, model: seq<A>)
    requires ModelAux(spine) == model
    ensures |spine| == |model|
    ensures forall i | 0 <= i < |spine| :: spine[i].data == model[i]
  {
    if spine == [] {
    } else {
      ModelRelationWithSpineAux(spine[1..], model[1..]);
    }
  }

  lemma ModelRelationWithSpine()
    requires Valid()
    ensures |spine| == |Model()|
    ensures forall i | 0 <= i < |spine| :: spine[i].data == Model()[i]
  {
    ModelRelationWithSpineAux(spine, Model());
  }

  function GetIndex(n: Node<A>): nat
    reads this, spine
    requires Valid()
    requires n in Repr()
    ensures 0 <= GetIndex(n) < |spine|
    ensures 0 <= GetIndex(n) < |Model()|
    ensures spine[GetIndex(n)] == n
    ensures forall i | 0 <= i < |spine| && spine[i] == n :: i == GetIndex(n)
  {
    ModelRelationWithSpine();
    DistinctSpine();
    var i :| 0 <= i < |spine| && spine[i] == n;
    i
  }

  method PopFront() returns (x: A)
    modifies this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
    /*private*/ ensures spine == old(spine[1..])
  {
    DistinctSpine();
    assert head in Repr();
    if head.next == null {
      HeadNextNullImpliesSingleton();
    } else {
      assert head == spine[0];
      assert head.IsPrevOf(spine[1]);
      assert spine[1] == head.next;
      assert head.next in Repr();
    }
    x := head.data;
    head := head.next;
    spine := spine[1..];
    if head != null {
      head.prev := null;
    }
  }

  method PushFront(x: A)
    modifies this, Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    /*private*/ ensures spine[1..] == old(spine)
  {
    var n := new Node(null, x, head);
    if head != null {
      head.prev := n;
    }
    head := n;
    /*GHOST*/ spine := [head] + spine;
    assert head !in old(Repr());
  }

  // Private method
  method Insert(mid: Node<A>, x: A)
    modifies this, Repr()
    requires Valid()
    requires mid in Repr()
    ensures Valid()
    ensures spine == Seq.Insert(mid.next, old(spine), old(GetIndex(mid))+1)
    ensures Model() == Seq.Insert(x, old(Model()), old(GetIndex(mid))+1)
    ensures mid.next != null
    ensures fresh(mid.next)
    ensures mid.next in spine
    ensures mid.next.next == old(mid.next)
    ensures forall n | n in old(spine) :: n in spine
  {
    { // GHOST
      DistinctSpine();
      ModelRelationWithSpine();
    }
    var n := new Node(mid, x, mid.next);
    assert n.prev == mid;
    assert n.prev == mid;
    ghost var i :| 0 <= i < |spine| && spine[i] == mid;
    if mid.next != null {
      assert spine[i+1] == mid.next;
      assert mid.next in Repr();
      mid.next.prev := n;
    }
    mid.next := n;
    { // GHOST
      spine := spine[..i+1] + [n] + spine[i+1..];
      ModelRelationWithSpine();
    }
  }

  // Private method
  method RemoveNext(mid: Node<A>)
    modifies this, Repr()
    requires Valid()
    requires mid in Repr()
    requires mid.next != null
    ensures Valid()
    ensures spine == Seq.Remove(old(spine), old(GetIndex(mid))+1)
    // Precondition needed for next line:
    ensures old(GetIndex(mid))+1 < old(|Model()|)
    ensures Model() == Seq.Remove(old(Model()), old(GetIndex(mid)+1))
    ensures mid.next == old(mid.next.next)
    ensures forall n | n in old(spine) && n != old(mid.next) :: n in spine
  {
    { // GHOST
      DistinctSpine();
      ModelRelationWithSpine();
    }
    ghost var i :| 0 <= i < |spine| && spine[i] == mid;
    assert spine[i+1] == mid.next;
    assert i+2 < |spine| ==> spine[i+2] == mid.next.next;
    mid.next := mid.next.next;
    if mid.next != null {
      mid.next.prev := mid;
    }
    { // GHOST
      spine := spine[..i+1] + spine[i+2..];
      ModelRelationWithSpine();
      assert Valid();
      assert GetIndex(mid) == old(GetIndex(mid));
      assert Model() == old(Seq.Remove(Model(), GetIndex(mid)+1));
    }
  }

  // Private method
  method FindPrev(mid: Node<A>) returns (prev: Node<A>)
    requires Valid()
    requires head != mid
    requires mid in Repr()
    ensures prev in Repr()
    ensures prev.next == mid
  {
    prev := head;
    ghost var i := 0;
    while prev.next != mid
      decreases |spine| - i
      invariant 0 <= i < |spine|
      invariant mid in spine[i+1..]
      invariant spine[i] == prev
    {
      assert spine[i+1] == prev.next;
      prev := prev.next;
      /*GHOST*/ i := i + 1;
    }
  }
}

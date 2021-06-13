include "../../../src/Utils.dfy"

type A = int

class CNode {
  var prev: CNode;
  var data: A;
  var next: CNode;

  constructor Phantom()
    ensures prev == this
    ensures next == this
  {
    prev := this;
    next := this;
  }

  constructor(prev: CNode, data: A, next: CNode)
    ensures this.prev == prev
    ensures this.data == data
    ensures this.next == next
  {
    this.prev := prev;
    this.data := data;
    this.next := next;
  }

  predicate IsPrevOf(n: CNode)
    reads this
  {
    next == n
  }

  predicate IsNextOf(n: CNode)
    reads this
  {
    prev == n
  }
}

class CircularDoublyLinkedList {
  var phantom: CNode;
  ghost var spine: seq<CNode>;

  function Repr(): set<object>
    reads this
  {
    set x | x in spine
  }

  predicate Valid()
    reads this, Repr()
  {
    && spine != []
    && phantom == spine[|spine|-1]
    && phantom !in spine[..|spine|-1]

    && (forall i | 0 <= i < |spine|-1 :: spine[i].next == spine[i+1])
    && spine[|spine|-1].next == spine[0]
    && (forall i | 0 <= i < |spine|-1 :: spine[i] == spine[i+1].prev)
    && spine[|spine|-1] == spine[0].prev
  }

  lemma ForallNextPrev(i: nat)
    requires 0 <= i < |spine|-1
    requires Valid()
    ensures spine[i].next == spine[i+1]
    ensures spine[i+1].prev == spine[i]
  {
    if i == 0 {
    } else {
    }
  }

  lemma DistinctSpineAux(n: nat)
    decreases |spine| - n
    requires Valid()
    requires 0 <= n <= |spine|
    ensures forall i, j | n <= i < j < |spine| :: spine[i] != spine[j]
  {
    if n == |spine| {
      assert spine[n..] == [];
    } else if n == |spine|-1 {
    } else {
      DistinctSpineAux(n+1);
      assert forall i, j | n+1 <= i < j < |spine| :: spine[i] != spine[j];
      if spine[n] in spine[n+1..] {
        var i: nat :| n+1 <= i < |spine| && spine[n] == spine[i];
        assert spine[i].next == spine[i+1];
        assert spine[n+1] == spine[i+1];
        assert false;
      }
      assert spine[n] !in spine[n+1..];
      assert forall i | n+1 <= i < |spine| :: spine[n] != spine[i];
    }
  }

  lemma DistinctSpine()
    requires Valid()
    ensures forall i, j | 0 <= i < j < |spine| :: spine[i] != spine[j]
  {
    DistinctSpineAux(0);
  }

  static function ModelAux(xs: seq<CNode>): seq<A>
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
    requires phantom.next != phantom  // head != null
    requires phantom.next.next == phantom
    ensures spine == [phantom.next, phantom]
  {
    if |spine| != 2 {
      assert |spine| >= 3;
      assert spine[0].next == spine[1];
      assert false;
    } else {
      assert spine == [phantom.next, phantom];
    }
  }

  function Model(): seq<A>
    reads this, spine
    requires Valid()
  {
    ModelAux(spine[..|spine|-1])
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    phantom := new CNode.Phantom();
    /*GHOST*/ spine := [phantom];
  }

  static lemma ModelRelationWithSpineAux(spine: seq<CNode>, model: seq<A>)
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
    ensures |spine|-1 == |Model()|
    ensures forall i | 0 <= i < |spine|-1 :: spine[i].data == Model()[i]
  {
    ModelRelationWithSpineAux(spine[..|spine|-1], Model());
  }

  function GetIndex(n: CNode): nat
    reads this, Repr()
    requires Valid()
    requires n in Repr()
    ensures 0 <= GetIndex(n) < |spine|
    ensures n != phantom ==> 0 <= GetIndex(n) < |Model()|
    ensures spine[GetIndex(n)] == n
    ensures forall i | 0 <= i < |spine| && spine[i] == n :: i == GetIndex(n)
  {
    ModelRelationWithSpine();
    DistinctSpine();
    var i :| 0 <= i < |spine| && spine[i] == n;
    i
  }

  lemma NextPrevIn(n: CNode)
    requires Valid()
    requires n in Repr()
    ensures n.next in Repr()
    ensures n.prev in Repr()
  {
    ghost var i := GetIndex(n);
    if i > 1 {
      assert spine[i].prev == spine[i-1];
    }
    if i < |spine|-1 {
      assert spine[i].next == spine[i+1];
      assert n.next in Repr();
    }
  }

  method Insert(mid: CNode, x: A)
    modifies this, mid, mid.prev
    requires Valid()
    requires mid in Repr()
    ensures Valid()
    ensures spine == Seq.Insert(mid.prev, old(spine), old(GetIndex(mid)))
    ensures mid != phantom ==> Model()
      == Seq.Insert(x, old(Model()), old(GetIndex(mid)))
    ensures mid == phantom ==> Model() == old(Model()) + [x]
    ensures fresh(mid.prev)
    ensures mid.prev in spine
    ensures mid.prev.prev == old(mid.prev)
    ensures forall n | n in old(spine) :: n in spine
  {
    { // GHOST
      DistinctSpine();
      ModelRelationWithSpine();
      assert GetIndex(mid) < |spine|;
    }
    var n := new CNode(mid.prev, x, mid);
    ghost var i := GetIndex(mid);
    { // GHOST
      assert spine[(i as int - 1) % |spine|] == mid.prev;
      NextPrevIn(mid);
    }
    mid.prev.next := n;
    mid.prev := n;
    { // GHOST
      spine := spine[..i] + [n] + spine[i..];
      ModelRelationWithSpine();
    }
  }

  method Remove(mid: CNode)
    modifies this, mid.prev, mid.next
    requires Valid()
    requires mid in Repr()
    requires mid != phantom
    ensures Valid()
    ensures spine == Seq.Remove(old(spine), old(GetIndex(mid)))
    ensures Model() == Seq.Remove(old(Model()), old(GetIndex(mid)))
    ensures mid.prev.next == old(mid.next)
    ensures forall n | n in old(spine) && n != mid :: n in spine
  {
    { // GHOST
      DistinctSpine();
      ModelRelationWithSpine();
    }
    ghost var i :| 0 <= i < |spine| && spine[i] == mid;
    { // GHOST
      assert spine[(i-1) % |spine|] == mid.prev;
      assert spine[i+1] == mid.next;
      NextPrevIn(mid);
    }
    mid.prev.next := mid.next;
    mid.next.prev := mid.prev;
    { // GHOST
      spine := spine[..i] + spine[i+1..];
      assert Valid();
      ModelRelationWithSpine();
      assert Valid();
      assert Model() == old(Seq.Remove(Model(), GetIndex(mid)));
    }
  }

  method PopFront() returns (x: A)
    modifies this, phantom, phantom.next.next
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
    ensures spine == old(spine[1..])
  {
    x := phantom.next.data;
    Remove(phantom.next);
  }

  method PushFront(x: A)
    modifies this, phantom, phantom.next
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures spine[1..] == old(spine)
  {
    Insert(phantom.next, x);
    assert fresh(phantom.next);
    assert phantom.next in Repr();
    assert phantom.next !in old(Repr());
  }
}

include "../../../src/Utils.dfy"

type A = int

class Node {
  var prev: Node;
  var data: A;
  var next: Node;

  constructor(prev: Node, data: A, next: Node)
    ensures this.prev == prev
    ensures this.data == data
    ensures this.next == next
  {
    this.prev := prev;
    this.data := data;
    this.next := next;
  }

  predicate IsPrevOf(n: Node)
    reads this
  {
    next == n
  }

  predicate IsNextOf(n: Node)
    reads this
  {
    prev == n
  }
}

class CircularDoublyLinkedList {
  var head: Node?;
  ghost var spine: seq<Node>;

  function Repr(): set<object>
    reads this
  {
    set x | x in spine
  }

  predicate Valid()
    reads this, Repr()
  {
    && (forall i | 1 <= i < |spine|-1 ::
        && spine[i].next == spine[i+1]
        && spine[i+1].prev == spine[i]
      )
    && (|spine| >= 2 ==>
        && spine[0].next == spine[1]
        && spine[1].prev == spine[0]
        && spine[|spine|-1].next == spine[0]
        && spine[0].prev == spine[|spine|-1]
      )
    && (if head == null then
        spine == []
      else
        && spine != []
        && spine[0] == head
        && head !in spine[1..]
      )
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
      // assert exists o :: spine[n..] == [o];
    } else {
      assert head != null;
      DistinctSpineAux(n+1);
      assert forall i, j | n+1 <= i < j < |spine| :: spine[i] != spine[j];
      if spine[n] in spine[n+1..] {
        var i: nat :| n+1 <= i < |spine| && spine[i] == spine[n];
        if i+1 < |spine| {
          assert spine[i].next == spine[i+1];
          assert i+1 != n+1;
          assert spine[n].next == spine[n+1];
          assert spine[n+1] == spine[i+1];
          assert false;
        } else {
          assert i == |spine|-1;
          assert head !in spine[1..];
          assert spine[n].next == spine[n+1];
          assert spine[n+1] == head;
          assert head in spine[1..];
          assert false;
        }
        assert false;
      }
      assert forall j | n+1 <= j < |spine| :: spine[n] != spine[j];
      assert forall i, j | n <= i < j < |spine| :: spine[i] != spine[j];
    }
  }

  lemma DistinctSpine()
    requires Valid()
    ensures forall i, j | 0 <= i < j < |spine| :: spine[i] != spine[j]
  {
    DistinctSpineAux(0);
  }

  static function ModelAux(xs: seq<Node>): seq<A>
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

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    head := null;
    /*GHOST*/ spine := [];
  }

  static lemma ModelRelationWithSpineAux(spine: seq<Node>, model: seq<A>)
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

  function GetIndex(n: Node): nat
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

  lemma NextPrevIndex(n: Node)
    requires Valid()
    requires n in Repr()
    requires n.next in Repr()
    requires n.prev in Repr()
    ensures GetIndex(n.next) == (GetIndex(n)+1) % |spine|
    ensures GetIndex(n.prev) == (GetIndex(n)-1) % |spine|

  lemma LastHasLastIndex(last: Node)
    requires Valid()
    requires last.next == null
    requires last in Repr()
    ensures GetIndex(last) == |spine|-1
  {
    var i := GetIndex(last);
    if i != |spine|-1 {
      assert spine[i].IsPrevOf(spine[i+1]);
      assert spine[i].next == spine[i+1];
      assert spine[i+1] != null;
      assert spine[i+1] == null;
      assert false;
    }
  }

  /*
  method PopFront() returns (x: A)
    modifies this, head.next
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
      ForallNextPrev(1);
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
    modifies this, head
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    // ensures old(head) != null ==> head != null
    // ensures old(head) != null && old(head.next) == null ==> head.next == null
    ensures spine[1..] == old(spine)
  {
    var n := new Node(null, x, head);
    if head != null {
      head.prev := n;
    }
    head := n;
    /*GHOST*/ spine := [head] + spine;
    assert head !in old(Repr());
  }
  */

  lemma NextPrevIn(n: Node)
    requires Valid()
    requires n in Repr()
    ensures n.next in Repr()
    ensures n.prev in Repr()

  /*
  method Insert(mid: Node, x: A)
    modifies this, Repr()
    requires Valid()
    requires mid in Repr()
    ensures Valid()
    ensures spine == Seq.Insert(mid.next, old(spine), old(GetIndex(mid))+1)
    ensures Model() == Seq.Insert(x, old(Model()), old(GetIndex(mid))+1)
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
    // ghost var i :| 0 <= i < |spine| && spine[i] == mid;
    ghost var i := GetIndex(mid);
    // assert mid.next in Repr();
    // assert mid.prev in Repr();
    NextPrevIn(mid);
    // assert spine[(i+1) % |spine|] == mid.next;
    // assert mid.next in Repr();
    mid.next.prev := n;
    mid.next := n;
    { // GHOST
      spine := spine[..i+1] + [n] + spine[i+1..];
      assert Valid();
      ModelRelationWithSpine();
    }
  }

  method RemoveNext(mid: Node)
    modifies this, Repr()
    requires Valid()
    requires mid in Repr()
    // requires mid.next != null
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
    mid.next.prev := mid;
    { // GHOST
      spine := spine[..i+1] + spine[i+2..];
      assert Valid();
      ModelRelationWithSpine();
      assert Valid();
      assert GetIndex(mid) == old(GetIndex(mid));
      assert Model() == old(Seq.Remove(Model(), GetIndex(mid)+1));
    }
  }
  */
}

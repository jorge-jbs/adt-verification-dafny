include "../../../src/Utils.dfy"

type A = int

class Node {
  var prev: Node;
  var data: A;
  var next: Node;

  constructor Phantom()
    ensures prev == this
    ensures next == this
  {
    prev := this;
    next := this;
  }

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
  var phantom: Node;
  ghost var spine: seq<Node>;

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

  /*
  lemma ForallNextPrevPrime(i: nat)
    requires Valid()
    ensures spine[i % |spine|].next == spine[(i+1) % |spine|]
    //ensures spine[i+1].prev == spine[i]
  {
    if i % |spine| == 0 {
      if |spine| == 1 {
      } else {
      }
    } else {
    }
  }
   */

  lemma DistinctSpineAux(n: nat)
    decreases |spine| - n
    requires Valid()
    requires 0 <= n <= |spine|
    ensures forall i, j | n <= i < j < |spine| :: spine[i] != spine[j]
    /*
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
       */

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
    phantom := new Node.Phantom();
    /*GHOST*/ spine := [phantom];
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
    ensures |spine|-1 == |Model()|
    ensures forall i | 0 <= i < |spine|-1 :: spine[i].data == Model()[i]
  {
    ModelRelationWithSpineAux(spine[..|spine|-1], Model());
  }

  function GetIndex(n: Node): nat
    reads this, Repr()
    requires Valid()
    requires n in Repr()
    // requires n != phantom
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

  lemma NextPrevIndex(n: Node)
    requires Valid()
    requires n in Repr()
    requires n != phantom
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

  lemma NextPrevIn(n: Node)
    requires Valid()
    requires n in Repr()
    ensures n.next in Repr()
    ensures n.prev in Repr()

    /*
  method PopFront() returns (x: A)
    modifies this, phantom, phantom.next.next
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
    ensures spine == old(spine[1..])
  {
    { // GHOST
      DistinctSpine();
      NextPrevIn(phantom.next);
      assert phantom.next.next in Repr();
      if phantom.next.next == phantom {
        HeadNextNullImpliesSingleton();
      } else {
        assert phantom.next == spine[0];
        ForallNextPrev(1);
        assert phantom.next.IsPrevOf(spine[1]);
        assert spine[1] == phantom.next.next;
        assert phantom.next.next in Repr();
      }
    }
    x := phantom.next.data;
    phantom.next := phantom.next.next;
    phantom.next.prev := phantom;
    { // GHOST
      spine := spine[1..];
      assert Valid();
      assert spine[..|spine|-1] == old(spine[1..|spine|-1]);
    }
  }
       */

  /*
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

  method Insert(mid: Node, x: A)
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
    var n := new Node(mid.prev, x, mid);
    ghost var i := GetIndex(mid);
    { //GHOST
      assert spine[(i-1) % |spine|] == mid.prev;
      NextPrevIn(mid);
    }
    mid.prev.next := n;
    mid.prev := n;
    { // GHOST
      spine := spine[..i] + [n] + spine[i..];
      ModelRelationWithSpine();
    }
  }

  method Remove(mid: Node)
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

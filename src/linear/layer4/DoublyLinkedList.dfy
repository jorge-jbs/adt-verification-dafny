include "../../../src/Utils.dfy"

class DNode<A> {
  var prev: DNode?<A>;
  var data: A;
  var next: DNode?<A>;

  constructor(prev: DNode?<A>, data: A, next: DNode?<A>)
    ensures this.prev == prev
    ensures this.data == data
    ensures this.next == next
  {
    this.prev := prev;
    this.data := data;
    this.next := next;
  }

  predicate IsPrevOf(n: DNode<A>)
    reads this
  {
    next == n
  }

  predicate IsNextOf(n: DNode<A>)
    reads this
  {
    prev == n
  }
}

class DoublyLinkedList<A> {
  var head: DNode?<A>;
  ghost var spine: seq<DNode<A>>;

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
    && if head == null then
        spine == []
      else
        && spine != []
        && spine[0] == head
        && spine[0].prev == null
        && spine[|spine|-1].next == null
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
    seq(|spine|, i reads this, spine requires 0 <= i < |spine| => spine[i].data)
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    head := null;
    /*GHOST*/ spine := [];
  }

  function GetIndex(n: DNode<A>): nat
    reads this, spine
    requires Valid()
    requires n in Repr()
    ensures 0 <= GetIndex(n) < |spine|
    ensures 0 <= GetIndex(n) < |Model()|
    ensures spine[GetIndex(n)] == n
    ensures forall i | 0 <= i < |spine| && spine[i] == n :: i == GetIndex(n)
  {
    DistinctSpine();
    var i :| 0 <= i < |spine| && spine[i] == n;
    i
  }

  lemma LastHasLastIndex(last: DNode<A>)
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

  lemma FirstHasFirstIndex(first: DNode<A>)
    requires Valid()
    requires first.prev == null
    requires first in Repr()
    ensures GetIndex(first) == 0
  {
    var i := GetIndex(first);
    if i != 0 {
      assert spine[i].prev == spine[i-1];
      assert spine[i-1] != null;
      assert spine[i-1] == null;
      assert false;
    }
  }

  lemma PrevHasPrevIndex(prev: DNode<A>, node: DNode<A>)
    requires Valid()
    requires prev in Repr()
    requires node in Repr()
    requires prev.IsPrevOf(node)
    ensures GetIndex(prev) == GetIndex(node)-1
  {
    var i := GetIndex(prev);
    assert prev.next == node;
    assert spine[i].next == spine[i+1];
    assert spine[i+1] == node;
  }

  method PopFront() returns (x: A)
    modifies this, head.next
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
    ensures spine == old(spine[1..])
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
    modifies this, head
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures spine == [head] + old(spine)
    ensures spine[1..] == old(spine)
  {
    var n := new DNode<A>(null, x, head);
    if head != null {
      head.prev := n;
    }
    head := n;
    /*GHOST*/ spine := [head] + spine;
    assert head !in old(Repr());
  }

  method InsertAfter(mid: DNode<A>, x: A)
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
    DistinctSpine();
    ghost var i :| 0 <= i < |spine| && spine[i] == mid;
    assert mid.next != null ==> mid.next == spine[i+1] && mid.next in Repr();
    var n := new DNode<A>(mid, x, mid.next);
    spine := spine[..i+1] + [n] + spine[i+1..];
    if n.next != null {
      n.next.prev := n;
    }
    mid.next := n;
    assert spine[i+1].prev == spine[i];
    assert Valid();
  }

  method InsertBefore(mid: DNode<A>, x: A)
    modifies this, Repr()
    requires Valid()
    requires mid in Repr()
    ensures Valid()
    ensures spine == Seq.Insert(mid.prev, old(spine), old(GetIndex(mid)))
    ensures Model() == Seq.Insert(x, old(Model()), old(GetIndex(mid)))
    ensures mid.prev != null
    ensures fresh(mid.prev)
    ensures mid.prev in spine
    ensures mid.prev.prev == old(mid.prev)
    ensures forall n | n in old(spine) :: n in spine
  {
    DistinctSpine();
    ghost var i :| 0 <= i < |spine| && spine[i] == mid;
    assert mid.prev != null ==> mid.prev == spine[i-1] && mid.prev in Repr();
    var n := new DNode<A>(mid.prev, x, mid);
    if mid.prev != null {
      mid.prev.next := n;
    } else {
      FirstHasFirstIndex(mid);
      head := n;
    }
    spine := spine[..i] + [n] + spine[i..];
    mid.prev := n;
    assert Valid();
  }

  method RemoveNext(mid: DNode<A>)
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
    DistinctSpine();
    ghost var i :| 0 <= i < |spine| && spine[i] == mid;
    assert spine[i+1] == mid.next;
    assert i+2 < |spine| ==> spine[i+2] == mid.next.next;
    mid.next := mid.next.next;
    if mid.next != null {
      mid.next.prev := mid;
    }
    spine := spine[..i+1] + spine[i+2..];
    assert Valid();
    assert GetIndex(mid) == old(GetIndex(mid));
    assert Model() == old(Seq.Remove(Model(), GetIndex(mid)+1));
  }

  method Remove(mid: DNode<A>)
    modifies this, Repr()
    requires Valid()
    requires mid in Repr()
    ensures Valid()
    ensures spine == Seq.Remove(old(spine), old(GetIndex(mid)))
    // Precondition needed for next line:
    ensures old(GetIndex(mid)) < old(|Model()|)
    ensures Model() == Seq.Remove(old(Model()), old(GetIndex(mid)))
    ensures old(mid.prev) != null ==> old(mid.prev).next == old(mid.next)
    ensures old(mid.next) != null ==> old(mid.next).prev == old(mid.prev)
    ensures old(mid.prev) == null ==> head == old(mid.next)
    ensures mid.next == old(mid.next)
    ensures mid.prev == old(mid.prev)
    ensures forall n | n in old(spine) && n != mid :: n in spine
    ensures forall n | n in old(spine) :: n != mid <==> n in spine

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    DistinctSpine();
    ghost var i :| 0 <= i < |spine| && spine[i] == mid;
    assert i == GetIndex(mid);
    if mid.prev != null {
      assert mid in Repr();
      assert mid.prev == spine[i].prev == spine[i-1];
      assert mid.prev in Repr();
      mid.prev.next := mid.next;
    } else {
      assert mid.prev == null;
      assert i >= 0;
      assert i > 0 ==> spine[i-1].prev == spine[i] == mid ==> false;
      assert i == 0;
      assert mid == head;
      if mid.next != null {
        head := mid.next;
      } else {
        assert |spine| >= 1;
        assert |spine| > 1 ==> spine[i].next == spine[i+1] ==> false;
        assert |spine| == 1;
        assert spine == [mid];
        head := null;
      }
    }
    if mid.next != null {
      assert mid in Repr();
      assert mid.next == spine[i+1];
      assert mid.next in Repr();
      mid.next.prev := mid.prev;
    }
    { // GHOST
      spine := spine[..i] + spine[i+1..];
      if mid.prev == null && mid.next == null {
        assert old(spine) == [mid];
        assert i == 0;
        assert spine == [];
      }
      assert Valid();
    }
  }
}

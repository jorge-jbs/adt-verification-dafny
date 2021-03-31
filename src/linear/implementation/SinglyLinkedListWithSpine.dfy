include "../../../src/Utils.dfy"

class SNode<A> {
  var data: A;
  var next: SNode?<A>;

  constructor(data: A, next: SNode?<A>)
    ensures this.data == data
    ensures this.next == next
  {
    this.data := data;
    this.next := next;
  }

  predicate IsPrevOf(n: SNode<A>)
    reads this
  {
    next == n
  }
}

class List<A> {
  var head: SNode?<A>;
  ghost var spine: seq<SNode<A>>;

  function Repr(): set<object>
    reads this
  {
    set x | x in spine
  }

  predicate Valid()
    reads this, Repr()
  {
    && (forall i | 0 <= i < |spine|-1 :: spine[i].IsPrevOf(spine[i+1]))
    && (if head == null then
        spine == []
      else
        spine != [] && spine[0] == head && spine[|spine|-1].next == null
      )
  }

  lemma HeadInSpine()
    requires Valid()
    ensures head != null ==> head in spine
  {
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

  lemma HeadNotInTail()
    requires Valid()
    requires head != null
    ensures head !in spine[1..]
  {
    DistinctSpine();
  }

  lemma NextNullImpliesLast(n: SNode<A>)
    requires Valid()
    requires n in spine
    requires n.next == null
    ensures spine[|spine|-1] == n
  {
    if spine[|spine|-1] != n {
      var i :| 0 <= i < |spine| && spine[i] == n;
      assert i != |spine|-1;
      assert spine[i].IsPrevOf(spine[i+1]);
      assert spine[i+1] == null;
      assert spine[i+1] != null;
      assert false;
    }
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

  static function ModelAux(xs: seq<SNode<A>>): seq<A>
    reads set x | x in xs :: x`data
  {
    if xs == [] then
      []
    else
      assert xs[0] in xs;
      assert forall x | x in xs[1..] :: x in xs;
      [xs[0].data] + ModelAux(xs[1..])
  }

  lemma ModelAuxCommutesConcat(xs: seq<SNode<A>>, ys: seq<SNode<A>>)
    ensures ModelAux(xs + ys) == ModelAux(xs) + ModelAux(ys)
  {
    if xs == [] {
      calc == {
        ModelAux(xs + ys);
        ModelAux([] + ys);
        { assert [] + ys == ys; }
        ModelAux(ys);
        [] + ModelAux(ys);
        ModelAux([]) + ModelAux(ys);
      }
    } else {
      assert xs == [xs[0]] + xs[1..];
      assert (xs + ys)[1..] == xs[1..] + ys;
      calc == {
        ModelAux(xs + ys);
        [xs[0].data] + ModelAux(xs[1..] + ys);
        { ModelAuxCommutesConcat(xs[1..], ys); }
        [xs[0].data] + ModelAux(xs[1..]) + ModelAux(ys);
        ModelAux(xs) + ModelAux(ys);
      }
    }
  }

  static lemma ModelRelationWithSpineAux(spine: seq<SNode<A>>, model: seq<A>)
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

  function Model(): seq<A>
    reads this, spine
    requires Valid()
  {
    ModelAux(spine)
  }

  // TODO: remove
  static function ModelUntilAux(xs: seq<SNode<A>>, last: SNode<A>): seq<A>
    reads set x | x in xs :: x`data
  {
    if xs == [] || xs[0] == last then
      []
    else
      assert xs[0] in xs;
      assert forall x | x in xs[1..] :: x in xs;
      [xs[0].data] + ModelUntilAux(xs[1..], last)
  }

  // TODO: remove
  function ModelUntil(last: SNode<A>): seq<A>
    reads this, spine
  {
    ModelUntilAux(spine, last)
  }

  function GetIndex(n: SNode<A>): nat
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

  lemma LastHasLastIndex(last: SNode<A>)
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

  lemma PrevHasPrevIndex(prev: SNode<A>, node: SNode<A>)
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

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    head := null;
    /*GHOST*/ spine := [];
  }

  method PopNode() returns (h: SNode<A>)
    modifies this
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [h] + spine == old(spine)
    ensures Repr() + {h} == old(Repr())
    ensures [h.data] + Model() == old(Model())
    ensures Repr() < old(Repr())
  {
    h := head;
    { // GHOST
      if head.next == null {
        HeadNextNullImpliesSingleton();
      }
      HeadNotInTail();
    }
    head := head.next;
    /*GHOST*/ spine := spine[1..];
    assert old(spine[0]) !in Repr();
    assert old(spine[0]) in old(Repr());
    assert Repr() < old(Repr());
  }

  method Pop() returns (res: A)
    modifies this
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [res] + Model() == old(Model())
    ensures Repr() < old(Repr())
    ensures spine == old(spine[1..])
  {
    var tmp := PopNode();
    res := tmp.data;
  }

  method PushNode(h: SNode<A>)
    modifies this, h`next
    requires Valid()
    requires h !in Repr()
    ensures Valid()
    ensures spine == [h] + old(spine)
    ensures Model() == [h.data] + old(Model())
    ensures Repr() > old(Repr())
    ensures Repr() == old(Repr()) + {h}
  {
    h.next := head;
    head := h;
    /*GHOST*/ spine := [head] + spine;
    assert head !in old(Repr());
  }

  method Push(x: A)
    modifies this
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures spine[1..] == old(spine)
  {
    var n := new SNode(x, null);
    PushNode(n);
  }

  method Append(other: List<A>)
    modifies this, Repr(), other
    requires Valid()
    requires other.Valid()
    // needed so that we don't build a cyclic list:
    requires Repr() !! other.Repr()
    ensures Valid()
    ensures Model() == old(Model() + other.Model())
    ensures Repr() == old(Repr() + other.Repr())
    ensures other.Valid()
    ensures other.Model() == []
    ensures other.Repr() == {}
  {
    if head == null {
      head := other.head;
      /*GHOST*/ spine := other.spine;
    } else {
      var last := head;
      ghost var i := 0;
      while last.next != null
        decreases |spine| - i
        invariant last != null
        invariant 0 <= i < |spine|
        invariant spine[i] == last
      {
        last := last.next;
        /*GHOST*/ i := i + 1;
      }
      /*GHOST*/ NextNullImpliesLast(last);
      last.next := other.head;
      /*GHOST*/ spine := spine + other.spine;
      /*GHOST*/ ModelAuxCommutesConcat(old(spine), other.spine);
    }
    other.head := null;
    /*GHOST*/ other.spine := [];
  }

  method PopPush(other: List<A>)
    modifies this, other, Repr(), other.Repr()
    requires head != null
    requires Valid()
    requires other.Valid()
    requires Repr() !! other.Repr()
    ensures Repr() !! other.Repr()
    ensures Valid()
    ensures other.Valid()
    ensures old(Repr()) > Repr()
    ensures Repr() + {old(head)} == old(Repr())
    ensures old(other.Repr()) < other.Repr()
    ensures other.Repr() == old(other.Repr()) + {old(head)}
    ensures Seq.Rev(old(Model())) + old(other.Model())
      == Seq.Rev(Model()) + other.Model()
  {
    var n := PopNode();
    other.PushNode(n);
  }

  method Reverse()
    modifies this, Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == Seq.Rev(old(Model()))
    ensures Repr() == old(Repr())
  {
    var aux := new List();
    aux.head := head;
    /*GHOST*/ aux.spine := spine;
    head := null;
    /*GHOST*/ spine := [];
    while aux.head != null
      decreases aux.Repr()
      invariant Valid()
      invariant aux.Valid()
      invariant Seq.Rev(old(Model())) == Seq.Rev(aux.Model()) + Model()
      invariant Repr() !! aux.Repr();
      invariant old(Repr()) == Repr() + aux.Repr()
    {
      aux.PopPush(this);
    }
  }

  method Insert(mid: SNode<A>, x: A)
    modifies this, mid
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
    var n := new SNode(x, mid.next);
    mid.next := n;
    { // GHOST
      ghost var i :| 0 <= i < |spine| && spine[i] == mid;
      spine := spine[..i+1] + [n] + spine[i+1..];
      assert Valid();
      ModelRelationWithSpine();
    }
  }

  method RemoveNext(mid: SNode<A>)
    modifies this, mid
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
    { // GHOST
      spine := spine[..i+1] + spine[i+2..];
      assert GetIndex(mid) == old(GetIndex(mid));
      ModelRelationWithSpine();
      assert Model() == old(Seq.Remove(Model(), GetIndex(mid)+1));
    }
  }

  method FindPrev(mid: SNode<A>) returns (prev: SNode<A>)
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

include "Utils.dfy"

class Node<A> {
  var data: A;
  var next: Node?<A>;

  constructor(data: A, next: Node?<A>)
    ensures this.data == data
    ensures this.next == next
  {
    this.data := data;
    this.next := next;
  }

  predicate IsPrevOf(n: Node<A>)
    reads this
  {
    next == n
  }
}

class List<A> {
  var head: Node?<A>;
  var spine: seq<Node<A>>;

  predicate Valid()
    reads this, spine
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

  static function ModelAux(xs: seq<Node<A>>): seq<A>
    reads multiset(xs)
  {
    if xs == [] then
      []
    else
      [xs[0].data] + ModelAux(xs[1..])
  }

  function Model(): seq<A>
    reads this, spine, multiset(spine)
    requires Valid()
  {
    ModelAux(spine)
  }

  constructor()
    ensures Valid()
    ensures Model() == []
  {
    head := null;
    spine := [];
  }

  method Pop() returns (res: A)
    modifies this
    requires head != null
    requires Valid()
    ensures Valid()
    ensures res == old(head.data)
    ensures [res] + Model() == old(Model())
    ensures [old(head)] + spine == old(spine)
  {
    res := head.data;
    if head.next == null {
      if |spine| != 1 {
        assert |spine| >= 2;
        assert spine[0].next == spine[1];
        assert false;
      } else {
        assert spine == [head];
      }
      assert spine == [head];
    }
    head := head.next;
    spine := spine[1..];
    if head == null {
      assert spine == [];
    }
  }

  method Push(x: A)
    modifies this
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures spine == [head] + old(spine)
    ensures fresh(Seq.Elems(spine) - old(Seq.Elems(spine)))
    ensures fresh(Seq.Elems(spine) - Seq.Elems(old(spine)))
    // ensures fresh(multiset(spine) - old(multiset(spine)))
    ensures fresh(head)
  {
    head := new Node(x, head);
    spine := [head] + spine;
  }

  method Append(other: List<A>)
    decreases spine
    modifies this
    requires Valid()
    requires other.Valid()
    // At first I didn't add the next precondition. In a language without
    // verification like C maybe I would have forgotten about it, but the function
    // doesn't work the way you expect it to if you don't keep this precondition
    // in mind. This could have resulted in segmentation faults or buggy code.
    // Another win for formal verification!
    requires this != other
    ensures Valid()
    ensures Model() == old(Model()) + other.Model()
  {
    if head == null {
      head := other.head;
      spine := other.spine;
    } else {
      var x := Pop();
      Append(other);
      Push(x);
    }
  }

  method PopPush(other: List<A>)
    modifies this, other
    requires head != null
    requires Valid()
    requires other.Valid()
    requires multiset(spine) !! multiset(other.spine)
    ensures multiset(spine) !! multiset(other.spine)
    ensures Valid()
    ensures other.Valid()
    // ensures Seq.Rev(old(spine)) + old(other.spine) == Seq.Rev(spine) + other.spine
    ensures old(multiset(spine)) > multiset(spine)
    ensures Seq.Rev(old(Model())) + old(other.Model())
      == Seq.Rev(Model()) + other.Model()
  {
    ghost var ospine := spine;
    ghost var ootherspine := other.spine;
    ghost var ohead := head;
    assert multiset(spine) !! multiset(other.spine);
    other.HeadInSpine();
    assert head in spine;
    if other.head == null {
      assert this != other;
    } else {
      assert other.head in other.spine;
      assert multiset(spine) !! multiset(other.spine);
      // assert forall x :: x in multiset(spine) ==> x !in multiset(other.spine);
      assert forall x :: x in multiset(spine) <== x !in multiset(other.spine);
      assert forall x :: x in multiset(spine) <==> x !in multiset(other.spine);
      assert forall xs: seq<A>, x: A :: x in xs <==> x in multiset(xs);
      Seq.InEquivInMultiset(spine);
      assert forall x :: x in spine <==> x in multiset(spine);
      assert forall x :: x in other.spine <==> x in multiset(other.spine);
      assert forall x :: x in spine <== x !in other.spine;
      assert head != other.head;
      assert this != other;
    }
    assert this != other;
    assert multiset(spine) !! multiset(other.spine);
    assert this != other;
    var x := Pop();
    assert this != other;
    assert multiset(spine) !! multiset(other.spine);
    assert this != other;
    other.Push(x);
    assert this != other;
    assert multiset(spine) !! multiset(other.spine);
  }

  method Reverse()
    modifies this
    requires Valid()
    ensures Valid()
    ensures Model() == Seq.Rev(old(Model()))
  {
    ghost var omodel := Model();
    var aux := new List();
    aux.head := head;
    aux.spine := spine;
    head := null;
    spine := [];
    while aux.head != null
      decreases multiset(aux.spine)
      invariant Valid()
      invariant aux.Valid()
      invariant Seq.Rev(omodel) == Seq.Rev(aux.Model()) + Model()
      invariant multiset(spine) !! multiset(aux.spine);
    {
      aux.PopPush(this);
    }
  }
}

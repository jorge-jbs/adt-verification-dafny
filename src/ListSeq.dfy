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

  function Repr(): set<object>
    reads this, spine
  {
    set x | x in spine
  }

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

  lemma HeadNotInTail()
    requires Valid()
    requires head != null
    ensures head !in spine[1..]

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
    // ensures res == old(head.data)
    ensures res == old(Model())[0]
    ensures [res] + Model() == old(Model())
    // ensures [old(head)] + spine == old(spine)
    ensures Repr() < old(Repr())
  {
    res := head.data;
    if head.next == null {  // Ghost code to prove `Valid()`
      if |spine| != 1 {
        assert |spine| >= 2;
        assert spine[0].next == spine[1];
        assert false;
      } else {
        assert spine == [head];
      }
      assert spine == [head];
    }
    HeadNotInTail();
    head := head.next;
    spine := spine[1..];
    if head == null {  // Ghost code to prove `Valid()`
      assert spine == [];
    }
    assert old(spine[0]) !in Repr();
    assert old(spine[0]) in old(Repr());
    assert Repr() < old(Repr());
  }

  method Push(x: A)
    modifies this
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    // ensures spine == [head] + old(spine)
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    // ensures fresh(head)
  {
    head := new Node(x, head);
    spine := [head] + spine;
    assert head !in old(Repr());
  }

  method Append(other: List<A>)
    decreases Repr()
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
    requires Repr() !! other.Repr()
    ensures Repr() !! other.Repr()
    ensures Valid()
    ensures other.Valid()
    ensures old(Repr()) > Repr()
    ensures old(other.Repr()) < other.Repr()
    ensures Seq.Rev(old(Model())) + old(other.Model())
      == Seq.Rev(Model()) + other.Model()
  {
    var x := Pop();
    other.Push(x);
  }

  method Reverse()
    modifies this
    requires Valid()
    ensures Valid()
    ensures Model() == Seq.Rev(old(Model()))
  {
    var aux := new List();
    aux.head := head;
    aux.spine := spine;
    head := null;
    spine := [];
    while aux.head != null
      decreases aux.Repr()
      invariant Valid()
      invariant aux.Valid()
      invariant Seq.Rev(old(Model())) == Seq.Rev(aux.Model()) + Model()
      invariant Repr() !! aux.Repr();
    {
      aux.PopPush(this);
    }
  }
}

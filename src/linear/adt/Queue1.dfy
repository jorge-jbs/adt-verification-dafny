include "../../../src/linear/implementation/DoublyLinkedListWithLast.dfy"
include "../../../src/linear/interface/Queue.dfy"

class Queue1 extends Queue {
  var list: DoublyLinkedListWithLast;

  function Depth(): nat
    ensures Depth() > 0
  {
    2
  }

  function Repr0(): set<object>
    reads this
  {
    {list}
  }

  function Repr1(): set<object>
    reads this, Repr0()
  {
    Repr0() + {list.list}
  }

  function Repr2(): set<object>
    reads this, Repr1()
  {
    Repr1() + list.Repr()
  }

  function ReprFamily(n: nat): set<object>
    decreases n
    requires n <= Depth()
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)
  {
    if n == 0 then
      Repr0()
    else if n == 1 then
      Repr1()
    else if n == 2 then
      Repr2()
    else
      assert false;
      {}
  }

  predicate Valid()
    reads this, Repr()
  {
    list.Valid()
  }

  function Model(): seq<int>
    reads this, Repr()
    requires Valid()
  {
    list.Model()
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    list := new DoublyLinkedListWithLast();
  }

  method Front() returns (x: int)
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[0]
  {
    x := list.Front();
  }

  method Enqueue(x: int)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
  {
    list.PushBack(x);
  }

  method Dequeue() returns (x: int)
    modifies Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
  {
    x := list.PopFront();
  }
}

class QueueIterator {
  ghost var index: nat
  ghost var parent: Queue1
  var node: Node?

  predicate Valid()
    reads this, parent, parent.Repr()
  {
    && parent.Valid()
    && ( node != null ==>
          && node in parent.list.list.Repr()
          && index == parent.list.list.GetIndex(node)
      )
  }

  constructor(l: Queue1)
    requires l.Valid()
    ensures Valid()
    ensures parent == l
  {
    index := 0;
    parent := l;
    node := l.list.list.head;
  }

  function method HasNext(): bool
    reads this
  {
    node != null
  }

  method Next() returns (x: int)
    modifies this
    requires HasNext()
    requires Valid()
    ensures Valid()
    ensures x == old(parent.Model()[index])
    ensures old(index) < index
    ensures parent == old(parent)
  {
    { // GHOST
      parent.list.list.ModelRelationWithSpine();
      if index < |parent.list.list.spine|-1 {
        assert parent.list.list.spine[index+1]
          == parent.list.list.spine[index].next;
      }
    }
    x := node.data;
    index := index + 1;
    node := node.next;
  }
}

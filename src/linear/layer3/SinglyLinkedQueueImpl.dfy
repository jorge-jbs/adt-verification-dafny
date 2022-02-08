include "../../../src/linear/layer1/Queue.dfy"
include "../../../src/linear/layer4/SinglyLinkedListWithLast.dfy"

class SinglyLinkedQueue extends Queue {
  var list: SinglyLinkedListWithLast<int>;

  function ReprDepth(): nat
    ensures ReprDepth() > 0
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
    requires n <= ReprDepth()
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

  lemma UselessLemma()
    ensures Repr() == ReprFamily(ReprDepth());
  {}

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

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []
  {
    list.list.head == null
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    list := new SinglyLinkedListWithLast();
  }

  function method Front(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Front() == Model()[0]
  {
    list.Front()
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

include "../../../src/linear/implementation/SinglyLinkedListWithSpine.dfy"
include "../../../src/linear/interface/Stack.dfy"

class Stack1 extends Stack {
  var list: List<int>;

  function Depth(): nat
  {
    1
  }

  function Repr0(): set<object>
    reads this
  {
    {list}
  }

  function Repr1(): set<object>
    reads this, Repr0()
  {
    {list} + list.Repr()
  }

  function ReprFamily(n: nat): set<object>
    decreases n
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)
  {
    if n == 0 then
      Repr0()
    else if n == 1 then
      Repr1()
    else
      ReprFamily(n-1)
  }

  lemma UselessLemma()
    ensures Repr() == ReprFamily(1);
  {}

  predicate Valid()
    reads this, Repr()
  {
    list.Valid()
  }

  function Model(): seq<int>
    reads this, list, list.spine
    requires Valid()
  {
    list.Model()
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    list := new List();
  }

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []
  {
    list.head == null
  }

  // O(1)
  method Top() returns (x: int)
    requires Valid()
    requires Model() != []
    ensures x == Model()[0]
  {
    x := list.head.data;
  }

  // O(1)
  method Push(x: int)
    modifies list
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures list == old(list)
  {
    list.Push(x);
  }

  // O(1)
  method Pop() returns (x: int)
    modifies list
    requires list.head != null
    requires Valid()
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
  {
    x := list.Pop();
  }
}

include "../../src/linear/ListSeq.dfy"

class Stack<A> {
  var list: List<A>;

  predicate Valid()
    reads this, list, list.spine
  {
    list.Valid()
  }

  function Repr(): set<object>
    reads this, list, list.spine
  {
    list.Repr()
  }

  function Model(): seq<A>
    reads this, list, list.spine
    requires Valid()
  {
    list.Model()
  }

  constructor()
    ensures Valid()
    ensures fresh(list)
    ensures Model() == []
    ensures Repr() == {}
  {
    list := new List();
  }

  // O(1)
  method Top() returns (x: A)
    requires Valid()
    requires Model() != []
    ensures x == Model()[0]
  {
    x := list.head.data;
  }

  // O(1)
  method Push(x: A)
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
  method Pop() returns (x: A)
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

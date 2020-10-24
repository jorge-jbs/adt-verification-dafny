include "../../src/linear/ListSeq.dfy"

class Queue<A> {
  var list: List<A>;
  var last: Node?<A>;

  predicate Valid()
    reads this, list, list.spine
  {
    list.Valid() && (last != null ==> (last in list.Repr() && last.next == null))
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
  {
    list := new List();
    last := null;
  }

  method Push(x: A)
    modifies list
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
  {
    list.Push(x);
  }

  /*
  method Pop() returns (res: A)
    modifies this, list
    requires list.head != null
    requires Valid()
    ensures Valid()
  {
    if list.head == last {
      last := null;
    }
    res := list.Pop();
    if list.head != last {
      assert Valid();
    }
  }
  */
}

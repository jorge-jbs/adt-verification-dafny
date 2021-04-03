include "../../../src/linear/implementation/DoublyLinkedList.dfy"

class DoublyLinkedListWithLast {
  var list: DoublyLinkedList;
  var last: DNode?;

  predicate Valid()
    reads this, list, list.spine
  {
    && list.Valid()
    && (if last == null then
        list.head == null
      else
        last in list.Repr() && last.next == null
      )
  }

  function Repr(): set<object>
    reads this, list
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
    ensures Model() == []
    ensures fresh(list)
    ensures last == null
    ensures fresh(Repr())
  {
    list := new DoublyLinkedList();
    last := null;
  }

  function method Front(): int
    reads this, list, list.Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Front() == Model()[0]
  {
    list.head.data
  }

  function method Back(): int
    reads this, list, list.Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Back() == Model()[|Model()|-1]
  {
    list.LastHasLastIndex(last);
    list.ModelRelationWithSpine();
    last.data
  }

  // O(1)
  method PushFront(x: A)
    modifies this, list, Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures list == old(list)
  {
    var ohead := list.head;
    { // GHOST
      if ohead != null {
        list.LastHasLastIndex(last);
      }
    }
    list.PushFront(x);
    if ohead == null {
      last := list.head;
    }
  }

  // O(1)
  method PopFront() returns (x: A)
    modifies this, list, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
    ensures list == old(list)
  {
    { // GHOST
      if list.head != null {
        list.LastHasLastIndex(last);
      }
    }
    if list.head == last {
      last := null;
    }
    { // GHOST
      if list.head.next != null {
        assert list.head == list.spine[0];
        assert list.head.next == list.spine[1];
        assert list.head.next in Repr();
      }
    }
    x := list.PopFront();
  }

  // O(1)
  method PushBack(x: A)
    modifies this, list, Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures list == old(list)
  {
    if last == null {
      assert Model() == [];
      list.PushFront(x);
      last := list.head;
    } else {
      { // GHOST
        list.LastHasLastIndex(last);
        list.ModelRelationWithSpine();
      }
      list.Insert(last, x);
      last := last.next;
      assert last != null;
      assert Valid();
    }
  }

  // O(1)
  method PopBack() returns (x: A)
    modifies this, list, list.Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Model() + [x] == old(Model())
    ensures Repr() < old(Repr())
    ensures list == old(list)
  {
    if list.head == last {
      assert list.head.next == null;
      list.HeadNextNullImpliesSingleton();
      assert list.spine == [list.head];
      calc == {
        list.Model();
        list.ModelAux(list.spine);
        [list.head.data];
      }
      x := list.head.data;
      list.head := null;
      /*GHOST*/ list.spine := [];
      last := null;
      assert old(list.Model()) == [x];
      assert Model() + [x] == old(Model());
      assert Repr() < old(Repr());
    } else {
      x := last.data;
      var prev := last.prev;
      { // GHOST
        list.ModelRelationWithSpine();
        list.LastHasLastIndex(last);
        assert last == list.spine[|list.spine|-1];
        assert last.prev == list.spine[|list.spine|-2];
        assert prev in Repr();
        assert last in Repr();
      }
      list.RemoveNext(prev);
      last := prev;
    }
  }
}

include "../../../src/linear/layer4/SinglyLinkedList.dfy"

class SinglyLinkedListWithLast<A> {
  var list: SinglyLinkedList<A>;
  var last: SNode?<A>;

  ghost function Repr(): set<object>
    reads this, list
  {
    list.Repr()
  }

  ghost predicate Valid()
    reads this, list, Repr()
  {
    && list.Valid()
      && (if last == null then
      list.head == null
      else
        last in list.Repr() && last.next == null
        )
  }

  ghost function Model(): seq<A>
    reads this, list, Repr()
    requires Valid()
  {
    list.Model()
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
    ensures fresh(list)
    ensures last == null
  {
    list := new SinglyLinkedList();
    last := null;
  }

  function Front(): A
    reads this, list, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Front() == Model()[0]
  {
    list.head.data
  }

  // O(1)
  method PushFront(x: A)
    modifies this, list
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures list == old(list)
  {
    var ohead := list.head;
    list.Push(x);
    if ohead == null {
      last := list.head;
    }
  }

  // O(1)
  method PopFront() returns (x: A)
    modifies this, list
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
    ensures list == old(list)
  {
    if list.head == last {
      last := null;
    }
    x := list.Pop();
  }

  // O(1)
  method PushBack(x: A)
    modifies this, last, list
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures list == old(list)
  {
    if last == null {
      assert Model() == [];
      list.Push(x);
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

  // O(n)
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
      /*GHOST*/ list.ModelRelationWithSpine();
      var prev := list.FindPrev(last);
      assert prev in Repr();
      assert last in Repr();
      /*GHOST*/ list.PrevHasPrevIndex(prev, last);
      list.RemoveNext(prev);
      x := last.data;
      last := prev;
      /*GHOST*/ list.LastHasLastIndex(last);
    }
  }
}

include "../../../src/linear/layer4/DoublyLinkedList.dfy"

class DoublyLinkedListWithLast<A> {
  var list: DoublyLinkedList<A>;
  var last: DNode?<A>;

  ghost predicate Valid()
    reads this, list, list.spine
  {
    && list.Valid()
    && (if last == null then
        list.head == null
      else
        last in list.Repr() && last.next == null
      )
  }

  ghost function Repr(): set<object>
    reads this, list
  {
    {list} + list.Repr()
  }

  ghost function Model(): seq<A>
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

  function Front(): A
    reads this, list, list.Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Front() == Model()[0]
  {
    list.head.data
  }

  function Back(): A
    reads this, list, list.Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Back() == Model()[|Model()|-1]
  {
    list.LastHasLastIndex(last);
    last.data
  }

  // O(1)
  method PushFront(x: A)
    modifies this, list, list.Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures list == old(list)
    ensures list.spine[1..] == old(list.spine)
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
    modifies this, list, list.Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
    ensures list == old(list)
    ensures [old(list.head)] + list.spine == old(list.spine);
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
    modifies this, list, list.Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures list == old(list)
    ensures list.spine == old(list.spine) + [last]
  {
    if last == null {
      assert Model() == [];
      list.PushFront(x);
      last := list.head;
    } else {
      { // GHOST
        list.LastHasLastIndex(last);
      }
      list.InsertAfter(last, x);
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
    ensures list.spine + [old(last)] == old(list.spine)
  {
    if list.head == last {
      assert list.head.next == null;
      list.HeadNextNullImpliesSingleton();
      assert list.spine == [list.head];
      assert list.Model() == [list.head.data];
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

  // Insertion after mid
  method InsertAfter(mid: DNode<A>, x: A)
    modifies this, Repr()
    requires Valid()
    requires mid in Repr()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures list.spine
      == Seq.Insert(mid.next, old(list.spine), old(list.GetIndex(mid))+1)
    ensures Model() == Seq.Insert(x, old(Model()), old(list.GetIndex(mid))+1)
    ensures mid.next != null
    ensures fresh(mid.next)
    ensures mid.next in list.spine
    ensures mid.next.next == old(mid.next)
    ensures forall n | n in old(list.spine) :: n in list.spine
    
    // ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    /*GHOST*/ list.LastHasLastIndex(last);
    list.InsertAfter(mid, x);
    if mid.next.next == null {
      last := mid.next;
    }
  }

  // Insertion before mid
  method InsertBefore(mid: DNode<A>, x: A)
    modifies this, Repr()
    requires Valid()
    requires mid in Repr()
    ensures Valid()
    ensures list.spine
      == Seq.Insert(mid.prev, old(list.spine), old(list.GetIndex(mid)))
    ensures Model() == Seq.Insert(x, old(Model()), old(list.GetIndex(mid)))
    ensures mid.prev != null
    ensures fresh(mid.prev)
    ensures mid.prev in list.spine
    ensures mid.prev.prev == old(mid.prev)
    ensures forall n | n in old(list.spine) :: n in list.spine
    requires forall x | x in Repr() :: allocated(x)
    // ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    /*GHOST*/ list.LastHasLastIndex(last);
    list.InsertBefore(mid, x);
    if list.head.next == null {
      last := list.head;
    }
  }

  method Remove(mid: DNode<A>)
    modifies this, Repr()
    requires Valid()
    requires mid in Repr()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures list.spine == Seq.Remove(old(list.spine), old(list.GetIndex(mid)))
    // Precondition needed for next line:
    ensures old(list.GetIndex(mid)) < old(|Model()|)
    ensures Model() == Seq.Remove(old(Model()), old(list.GetIndex(mid)))
    ensures old(mid.prev) != null ==> old(mid.prev).next == old(mid.next)
    ensures old(mid.next) != null ==> old(mid.next).prev == old(mid.prev)
    ensures forall n | n in old(list.spine) && n != mid :: n in list.spine

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    ghost var i :| 0 <= i < |list.spine| && list.spine[i] == mid;
    list.DistinctSpine();
    if mid != last {
      list.LastHasLastIndex(last);
      assert list.spine[|list.spine|-1] == last;
      list.Remove(mid);
      assert forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x);
      assert list.spine[|list.spine|-1] == last;
      assert last in list.Repr();
      assert last.next == null;
      assert Valid();
    } else {
      list.LastHasLastIndex(mid);
      assert i == |list.spine|-1;
      var prev := mid.prev;
      assert prev != null ==> list.spine[i-1] == prev;
      list.Remove(mid);
      assert forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x);
      assert prev != null ==> list.spine[i-1] == prev;
      last := prev;
      assert last != null ==> last in list.Repr();
      assert last != null ==> last.next == null;
      assert Valid();
    }
    assert forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x);
  }
}

include "../../../src/linear/layer1/Deque.dfy"
include "../../../src/linear/layer4/DoublyLinkedListWithLast.dfy"

class LinkedDequeImpl<A> extends Deque<A> {
  var list: DoublyLinkedListWithLast<A>
  var size: nat

  ghost function Repr0(): set<object>
    reads this
  {
    {list}
  }

  ghost function Repr1(): set<object>
    reads this, Repr0()
  {
    Repr0() + {list.list}
  }

  ghost function Repr2(): set<object>
    reads this, Repr1()
  {
    Repr1() + list.Repr()
  }

  ghost function ReprFamily(n: nat): set<object>
    decreases n
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
      ReprFamily(n-1)
  }

  ghost predicate Valid()
    reads this, Repr()
  {
    && ReprDepth == 2
    && list.Valid()
    && size == |list.Model()|
  }

  ghost function Model(): seq<A>
    reads this, Repr()
    requires Valid()
  {
    list.Model()
  }

  method Empty() returns (b:bool)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures b==Empty?() 
  {
    return list.list.head == null;
  }

  method Size() returns (s:nat)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures s == |Model()| 
  {
    return size;
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    ReprDepth := 2;
    list := new DoublyLinkedListWithLast();
    size := 0;
  }

  method Front() returns (x:A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[0]
  {
    return list.Front();
  }

  method PushFront(x: A)
    modifies this, Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
  {
    list.PushFront(x);
    size := size + 1;
  }

  method PopFront() returns (x: A)
    modifies this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
  {
    x := list.PopFront();
    size := size - 1;
  }

  method Back() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[|Model()|-1]
  {
    return list.Back();
  }

  method PushBack(x: A)
    modifies this, Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
  {
    list.PushBack(x);
    size := size + 1;
  }

  method PopBack() returns (x: A)
    modifies this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Model() + [x] == old(Model())
    ensures Repr() < old(Repr())
  {
    x := list.PopBack();
    size := size - 1;
  }
}

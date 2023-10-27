include "../Deque/DequeSpec.dfy"
include "../DataStructures/DoublyLinkedListWithLast.dfy"

module DoublyLinkedDequeImpl{
  import opened DequeSpec
  import opened DoublyLinkedListWithLast

  export provides DequeSpec
         reveals DoublyLinkedDequeImpl
         provides DoublyLinkedDequeImpl.Model, DoublyLinkedDequeImpl.Valid, DoublyLinkedDequeImpl.ReprFamily
         provides DoublyLinkedDequeImpl.Empty, DoublyLinkedDequeImpl.Size
         provides DoublyLinkedDequeImpl.Front, DoublyLinkedDequeImpl.PushFront, DoublyLinkedDequeImpl.PopFront
         provides DoublyLinkedDequeImpl.Back, DoublyLinkedDequeImpl.PushBack, DoublyLinkedDequeImpl.PopBack

class DoublyLinkedDequeImpl<A> extends Deque<A> {
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
    && assert Repr0() <= ReprFamily(2); true
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
    x := list.Front();
  }

  method PushFront(x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
  {
    list.PushFront(x);
    size := size + 1;
  }

  method PopFront() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures [x] + Model() == old(Model())
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
    x := list.Back();
  }

  method PushBack(x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
  {
    list.PushBack(x);
    size := size + 1;
  }

  method PopBack() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() + [x] == old(Model())
  {
    x := list.PopBack();
    size := size - 1;
  }
}

}
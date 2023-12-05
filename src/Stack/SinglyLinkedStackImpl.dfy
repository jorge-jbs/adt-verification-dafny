include "StackSpec.dfy"
include "../DataStructures/SinglyLinkedList.dfy"

module SinglyLinkedStackImpl{
  import opened StackSpec
  import opened SinglyLinkedList

   export provides StackSpec
          reveals SinglyLinkedStackImpl
          provides SinglyLinkedStackImpl.Model, SinglyLinkedStackImpl.Valid, SinglyLinkedStackImpl.ReprFamily
          provides SinglyLinkedStackImpl.Empty, SinglyLinkedStackImpl.Size
          provides SinglyLinkedStackImpl.Top, SinglyLinkedStackImpl.Push, SinglyLinkedStackImpl.Pop

class SinglyLinkedStackImpl<A> extends Stack<A> {
  var list: SinglyLinkedList<A>
  var size: nat

  ghost function Repr0(): set<object>
    reads this
  {
    {list}
  }

  ghost function Repr1(): set<object>
    reads this, Repr0()
  {
    {list} + list.Repr()
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
    else
      ReprFamily(n-1)
  }

  ghost predicate Valid()
    reads this, Repr()
  {
    && ReprDepth == 1
    && assert Repr0() <= ReprFamily(1);true
    && list.Valid()
    && size == |list.Model()|
  }

  ghost function Model(): seq<A>
    reads this, Repr()
    requires Valid()
  {
    list.Model()
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
    ensures allocated(Repr())
  {
    ReprDepth := 1;
    list := new SinglyLinkedList();
    size := 0;
  }

  method Empty() returns (b: bool)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())
    
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures b == Empty?() 
  {
    b := list.head == null;
  }

  method Size() returns (s:nat)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures s==|Model()| 
  {
    return size;
  }

  // O(1)
  method Top() returns (x: A)
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
    return list.head.data;
  }

  // O(1)
  method Push(x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
  {
    list.Push(x);
    size := size + 1;
  }

  // O(1)
  method Pop() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())
    
    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures [x] + Model() == old(Model())
  {
    x := list.Pop();
    size := size - 1;
  }
}
}


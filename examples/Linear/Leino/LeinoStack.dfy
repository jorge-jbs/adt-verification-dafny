include "../../../src/Stack/StackSpec.dfy"
include "LeinoList.dfy"

module LeinoStack{
  import opened StackSpec
  import opened LeinoList

class LeinoStack<A> extends Stack<A> {
  var head: LNode?<A>

  ghost function Repr0(): set<object>
    reads this
  {
    if head == null then
      {this}
    else
      {this, head}
  }

  ghost function Repr1(): set<object>
    reads this, Repr0()
  {
    if head == null then
      Repr0()
    else
      Repr0() + head.repr
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
    && assert Repr0() <= ReprFamily(1); true
    && (head != null ==> head.Valid())
  }

  ghost function Model(): seq<A>
    reads this, Repr()
    requires Valid()
  {
    if head == null then
      []
    else
      head.model
  }

  constructor()
    ensures Valid()
  {
    ReprDepth := 1;
    head := null;
  }

  method Empty() returns (b: bool)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())
    
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures b == Empty?() 

  {
    b := head == null;
  }

  method Size() returns (s: nat)//TO DO
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures s == |Model()| 

  method Top() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[0]

  {
    x := head.data;
  }

  method Pop() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures [x] + Model() == old(Model())
  {
    x := head.data;
    head := head.next;
  }

  method Push(x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
  {
    head := new LNode(x, head);
  }
}

}
include "../src/linear/layer1/Stack.dfy"
include "../extra/LeinoList.dfy"

class LeinoStack<A> extends Stack<A> {
  var head: LNode?<A>;

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

  function Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []
  {
    head == null
  }

  function Top(): A
    reads this, Repr()
    requires Valid()
    requires !Empty()
    ensures Valid()
    ensures Top() == Model()[0]
  {
    head.data
  }

  method Pop() returns (x: A)
    modifies Repr()
    requires Valid()
    requires !Empty()
    ensures Valid()
    ensures [x] + Model() == old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    x := head.data;
    head := head.next;
  }

  method Push(x: A)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    head := new LNode(x, head);
  }
}

include "../../../src/linear/layer1/ADT.dfy"

trait Stack<A> extends ADT<seq<A>> {
  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []

  function method Top(): A
    reads this, Repr()
    requires Valid()
    requires !Empty()
    ensures Valid()
    ensures Top() == Model()[0]

  method Push(x: A)
    modifies this, Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

  method Pop() returns (x: A)
    modifies this, Repr()
    requires Valid()
    requires !Empty()
    ensures Valid()
    ensures [x] + Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
}

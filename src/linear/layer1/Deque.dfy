trait Dequeue<A> {
  function ReprDepth(): nat
    ensures ReprDepth() > 0

  function ReprFamily(n: nat): set<object>
    decreases n
    requires n <= ReprDepth()
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)

  function Repr(): set<object>
    reads this, ReprFamily(ReprDepth()-1)
  {
    ReprFamily(ReprDepth())
  }

  lemma UselessLemma()
    ensures Repr() == ReprFamily(ReprDepth());

  predicate Valid()
    reads this, Repr()

  function Model(): seq<A>
    reads this, Repr()
    requires Valid()

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []

  function method Front(): A
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Front() == Model()[0]

  method PushFront(x: A)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

  method PopFront() returns (x: A)
    modifies Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [x] + Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

  function method Back(): A
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Back() == Model()[|Model()|-1]

  method PushBack(x: A)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

  method PopBack() returns (x: A)
    modifies Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Model() + [x] == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
}

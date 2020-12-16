trait Stack {
  function Depth(): nat
    ensures Depth() > 0

  function ReprFamily(n: nat): set<object>
    decreases n
    requires n <= Depth()
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)

  function Repr(): set<object>
    reads this, ReprFamily(Depth()-1)
    // ensures Repr() == ReprFamily(Depth())
  {
    ReprFamily(Depth())
  }

  lemma UselessLemma()
    ensures Repr() == ReprFamily(Depth());

  predicate Valid()
    reads this, Repr()

  function Model(): seq<int>
    reads this, Repr()
    requires Valid()

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []

  method Top() returns (x: int)
    requires Valid()
    requires !Empty()
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[0]

  method Push(x: int)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))

  method Pop() returns (x: int)
    modifies Repr()
    requires Valid()
    requires !Empty()
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
}

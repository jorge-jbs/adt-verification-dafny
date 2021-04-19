trait List {
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

  function Iterators(): set<ListIterator>
    reads this, Repr()
    ensures forall it | it in Iterators() ::
      && it.Parent() == this
      && {it} !! {this} + Repr()

  function ValidIterators(): set<ListIterator>
    reads this, Repr()
    ensures ValidIterators() <= Iterators()

  // predicate ValidIterator(it: ListIterator)
  //   reads this, Repr(), it
  //   requires Valid()

  predicate Valid()
    reads this, Repr()

  function Model(): seq<int>
    reads this, Repr()
    requires Valid()

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []

  function method Size(): nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|

  method At(i: nat) returns (x: int)
    requires Valid()
    requires i < |Model()|

    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[i]
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

  method GetIterator(i: nat) returns (it: ListIterator)
    modifies this, Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures Iterators() == {it} + old(Iterators())
    // ensures it !in old(Iterators())
    // ensures it in Iterators()
    ensures it.Index() == i
    // ensures ValidIterator(it)
    // ensures it.Valid()
    ensures fresh(it)
    ensures it in ValidIterators()
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

  method IAt(it: ListIterator) returns (x: int)
    requires Valid()
    requires it.Parent() == this
    requires {it} !! {this}
    requires it.Index() < |Model()|

    ensures Valid()
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    ensures it.Index() == old(it.Index())
    ensures it.Parent() == old(it.Parent())
    ensures Model() == old(Model())

    ensures x == Model()[it.Index()]

  function method Front(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Front() == Model()[0]

  method PushFront(x: int)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

  method PopFront() returns (x: int)
    modifies Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [x] + Model() == old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    // ensures Iterators() <= old(Iterators())
    // ensures forall it | it in old(Iterators()) :: it.Parent() == old(it.Parent())
    // ensures forall it | it in old(Iterators()) && it.Index() == 0 :: it !in Iterators()

    ensures Iterators() == old(Iterators())
    ensures ValidIterators() <= old(ValidIterators())
    ensures forall it | it in Iterators() && it in old(ValidIterators()) ::
      if it.Index() == 0 then
        it !in ValidIterators()
      else
        it in ValidIterators()

  function method Back(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Back() == Model()[|Model()|-1]

  method PushBack(x: int)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

  method PopBack() returns (x: int)
    modifies Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Model() + [x] == old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures ValidIterators() <= old(ValidIterators())
    ensures forall it | it in Iterators() && it in old(ValidIterators()) ::
      if it.Index() == old(|Model()|-1) then
        it !in ValidIterators()
      else
        it in ValidIterators()
}

trait ListIterator {
  function Parent(): List
    reads this
    ensures {Parent()} !! {this}

  function Index(): nat
    reads this, Parent(), Parent().Repr()
    requires Parent().Valid()
    ensures Index() < |Parent().Model()|

  function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Parent().Valid()
    ensures HasNext() <==> Index() < |Parent().Model()|

  // predicate Valid()
  //   reads this, Parent(), Parent().Repr()
  //   requires Parent().Valid()

  method Next() returns (x: int)
    modifies this
    requires {this} !! {Parent()} + Parent().Repr()
    requires Parent().Valid()
    requires this in Parent().ValidIterators()
    // requires Valid()
    requires HasNext()
    requires |Parent().Model()| > 0
    ensures Parent().Valid()
    ensures this in Parent().ValidIterators()
    ensures old(Index()) < Index()
    ensures old(Parent()) == Parent()
    ensures x == Parent().Model()[old(Index())]
    ensures Index() == 1 + old(Index())

    // Esto no funciona pero no sé por qué:
    //ensures old(Parent().Model()) == Parent().Model()
    //ensures x == old(Parent().Model()[Index()])
}

method ItertatorExample(l: List, v: array<int>)
  modifies l, l.Repr()
  modifies v
  requires {v} !! {l} + l.Repr()
  requires l.Valid()
  requires v.Length == |l.Model()|
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures v[..] == l.Model()  // parece que esta poscondición siempre es demostrada (bug de Dafny?)
{
  var it := l.GetIterator(0);
  var i := 0;
  // var it := new QueueIterator(l);
  while it.HasNext()
    modifies it, v
    decreases |l.Model()| - it.Index()
    invariant l.Model() == old(l.Model())
    invariant l.Valid()
    invariant it in l.ValidIterators()
    invariant {it} !! {l} + l.Repr()
    invariant it.Index() == i
    invariant i < |l.Model()|
    invariant v[..i] == l.Model()[..i]
  {
    var x := it.Next();
    assert x == l.Model()[i];
    v[i] := x;  // si quito esta línea funciona igualmente .-.
    // print(x);
    i := i + 1;
  }
}

trait ListIterator {
  function Parent(): List
    reads this

  predicate Valid()
    reads this, Parent(), Parent().Repr()

  function Index(): nat
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures Index() <= |Parent().Model()|
    ensures HasNext() <==> Index() < |Parent().Model()|
    ensures !HasNext() <==> Index() == |Parent().Model()|

  function method HasNext(): bool
    reads this

  method Next() returns (x: int)
    modifies this
    requires HasNext()
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Iterators() :: allocated(it)
    ensures Parent().Valid()
    ensures Valid()
    ensures old(Index()) < Index()
    ensures old(Parent()) == Parent()
    ensures old(Index()) < |Parent().Model()|
    ensures old(Parent().Model()) == Parent().Model()
    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures x == Parent().Model()[old(Index())]
    ensures Index() == 1 + old(Index())
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Index() == old(it.Index()))
    ensures forall x | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures forall x | x in Parent().Repr() :: allocated(x)
}

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

  function Iterators(): set<ListIterator>
    reads this, Repr()
    requires Valid()
    // ensures Iterators() <= Repr();
    ensures forall it | it in Iterators() :: it in Repr() &&  it.Parent() == this

  method Begin() returns (it: ListIterator)
    modifies this, Repr()
    requires Valid()
    requires forall it | it in Iterators() :: allocated(it)
    ensures Valid()
    ensures Model() == old(Model())
    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Index() == 0
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

  function method Front(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Front() == Model()[0]

  method PushFront(x: int)
    modifies this, Repr()
    requires Valid()
    // requires forall x | x in Repr() :: allocated(x)
    requires forall x | x in Iterators() :: allocated(x)
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in Iterators() && old(it.Valid()) :: it.Valid()

  method PopFront() returns (x: int)
    modifies this, Repr()
    requires Valid()
    requires Model() != []
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures [x] + Model() == old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in Iterators() && old(it.Valid()) ::
      if old(it.Index()) == 0 then
        !it.Valid()
      else
        it.Valid() && it.Index() + 1 == old(it.Index())

  function method Back(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Back() == Model()[|Model()|-1]

  method PushBack(x: int)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + [x]

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in Iterators() && old(it.Valid()) :: it.Valid()

  method PopBack() returns (x: int)
    modifies this, Repr()
    requires Valid()
    requires Model() != []
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() + [x] == old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in Iterators() && old(it.Valid()) ::
      if old(it.Index()) == old(|Model()|-1)  then
        !it.Valid()
      else if old(it.Index()) == old(|Model()|) then
        it.Valid() && it.Index() + 1 == old(it.Index())
      else
        it.Valid() && it.Index() == old(it.Index())
}

lemma Obvious(x: object)
  ensures allocated(x)
{}

lemma Obviouss(os: set<object>)
  ensures forall x | x in os :: allocated(x)
{
  forall x | x in os
    ensures allocated(x)
  {
    Obvious(x);
  }
}

method ItertatorExample1(l: List, v: array<int>)
  modifies l, l.Repr(), v
  requires {v} !! {l} + l.Repr()
  requires l.Valid()
  requires v.Length == |l.Model()|
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures v[..] == l.Model()
{
  Obviouss(l.Iterators());
  var it := l.Begin();
  var i := 0;
  while it.HasNext()
    decreases |l.Model()| - it.Index()
    invariant l.Valid()
    invariant l.Model() == old(l.Model())
    invariant it.Parent() == l
    invariant it.Valid()
    invariant {it} !! {l}
    invariant {v} !! {l} + l.Repr()
    invariant {v} !! {it}
    invariant it.Index() == i
    invariant i <= |l.Model()|
    invariant v[..i] == l.Model()[..i]
    invariant forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
    invariant forall x | x in l.Repr() :: allocated(x)
  {
    var x := it.Next();
    v[i] := x;
    i := i + 1;
  }
}

method ItertatorExample2(l: List)
  modifies l, l.Repr()
  requires l.Valid()
  requires l.Model() != []
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
{
  Obviouss(l.Iterators());
  var it1 := l.Begin();
  var x := it1.Next();
}

method ItertatorExample3(l: List)
  modifies l, l.Repr()
  requires l.Valid()
  requires l.Model() != []
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
{
  Obviouss(l.Iterators());
  var it1 := l.Begin();
  var it2 := l.Begin();
  assert it2.Valid();
  assert it2.Index() == 0;
  assert it2.Index() < |l.Model()|;
  assert it2.HasNext();
  assert it1.Valid();
  assert it1.Index() == 0;
  assert it1.Index() < |l.Model()|;
  assert it1.HasNext();
  var x := it2.Next();
}

method ItertatorExample4(l: List)
  modifies l, l.Repr()
  requires l.Valid()
  requires l.Model() != []
  ensures l.Valid()
{
  /*GHOST*/ Obviouss(l.Iterators());
  var it1 := l.Begin();
  var it2 := l.Begin();
  var x := it2.Next();
  var y := l.PopFront();
  assert x == y;
  assert !it1.Valid();
  assert it2.Valid();
}

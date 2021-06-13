include "../../../src/Utils.dfy"
include "../../../src/linear/adt/List.dfy"

trait LinkedListIterator /*extends ListIterator*/ {
  function Parent(): LinkedList //List
    reads this

  predicate Valid()
    reads this, Parent(), Parent().Repr()

  function Index(): nat
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures Index() <= |Parent().Model()|

  function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext() <==> Index() < |Parent().Model()|

  method Next() returns (x: int)
    modifies this
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    requires allocated(Parent())
    requires forall it | it in Parent().Repr() :: allocated(it)
    ensures Parent().Valid()
    ensures Valid()
    ensures old(Index()) < Index()
    ensures old(Parent()) == Parent()
    ensures old(Parent().Model()) == Parent().Model()
    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures x == Parent().Model()[old(Index())]
    ensures Index() == 1 + old(Index())
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Index() == old(it.Index()))
    ensures forall x | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures forall x | x in Parent().Repr() :: allocated(x)

  function method Peek(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() == Parent().Model()[Index()]

  method Copy() returns (it: LinkedListIterator) //ListIterator)
    modifies Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Iterators() :: allocated(it)
    ensures fresh(it)
    ensures Valid()
    ensures it.Valid()
    ensures Parent().Valid()
    ensures it in Parent().Iterators()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == old(Parent())
    ensures Parent() == it.Parent()
    ensures Index() == it.Index()
    ensures it.Valid()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())
    ensures Parent().Model() == old(Parent().Model())
    ensures forall x | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures forall x | x in Parent().Repr() :: allocated(x)
}

trait LinkedList /*extends List*/ {
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

  function Iterators(): set<LinkedListIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this

  method Begin() returns (it: LinkedListIterator) //ListIterator)
    modifies this, Repr()
    requires Valid()
    requires forall it | it in Iterators() :: allocated(it)
    ensures Valid()
    ensures Model() == old(Model())
    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Index() == 0
    ensures it.Parent() == this
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
    ensures forall it | it in Iterators() && old(it.Valid()) ::
      it.Valid() // && it.Index() == old(it.Index()) + 1

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
        it.Valid() // && it.Index() + 1 == old(it.Index())
    // ensures forall it | it in Iterators() && old(it.Valid()) && old(it.Index()) != 0 ::
    //   it.Valid() && it.Index() + 1 == old(it.Index())

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
    ensures forall it | it in Iterators() && old(it.Valid()) ::
      it.Valid() // && it.Index() == old(it.Index())

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

  method Insert(mid: LinkedListIterator, x: int)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == Seq.Insert(x, old(Model()), old(mid.Index())+1)
    ensures Iterators() == old(Iterators())
    ensures forall it | it in Iterators() && old(it.Valid()) :: it.Valid()
    ensures forall it | it in Iterators() && old(it.Valid()) ::
      if old(it.Index()) <= old(mid.Index())  then
        it.Index() == old(it.Index())
      else
        it.Index() == old(it.Index()) + 1
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
}

method FillArray(l: List, v: array<int>)
  modifies l, l.Repr(), v
  requires {v} !! {l} + l.Repr()
  requires l.Valid()
  requires v.Length == |l.Model()|
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures v[..] == l.Model()
  ensures forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() :: allocated(x)
{
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

method IteratorExample1(l: List)
  modifies l, l.Repr()
  requires l.Valid()
  requires l.Model() != []
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() :: allocated(x)
{
  var it1 := l.Begin();
  var x := it1.Next();
}

method IteratorExample2(l: List)
  modifies l, l.Repr()
  requires l.Valid()
  requires l.Model() != []
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() :: allocated(x)
{
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

method IteratorExample3(l: LinkedList)
  modifies l, l.Repr()
  requires l.Valid()
  requires l.Model() != []
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() :: allocated(x)
{
  var it1 := l.Begin();
  var it2 := l.Begin();
  var x := it2.Next();
  var y := l.PopFront();
  assert x == y;
  assert !it1.Valid();
  assert it2.Valid();
}

method FindMax(l: LinkedList) returns (max: LinkedListIterator)
  modifies l, l.Repr()
  requires l.Valid()
  requires l.Model() != []
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures fresh(max)
  ensures max.Valid()
  ensures max.Parent() == l
  ensures max.HasNext()
  ensures forall x | x in l.Model() :: l.Model()[max.Index()] >= x
  ensures forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() :: allocated(x)
  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) ::
    it.Valid() && it.Index() == old(it.Index())
{
  max := l.Begin();
  var it := l.Begin();
  while it.HasNext()
    decreases |l.Model()| - it.Index()
    invariant l.Valid()
    invariant l.Model() == old(l.Model())
    invariant it.Valid()
    invariant it.Parent() == l
    invariant it in l.Iterators()
    invariant fresh(max)
    invariant max.Valid()
    invariant max.Parent() == l
    invariant max in l.Iterators()
    invariant max != it
    invariant max.HasNext()
    invariant it.Index() <= |l.Model()|
    invariant forall k | 0 <= k < it.Index() :: l.Model()[max.Index()] >= l.Model()[k]
    invariant forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
    invariant forall x | x in l.Repr() :: allocated(x)
    invariant forall x | x in old(l.Repr()) :: allocated(x)
    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())
  {
    if it.Peek() > max.Peek() {
      max := it.Copy();
    }
    var x := it.Next();
  }
}


function Dup<A>(xs: seq<A>): seq<A>
{
  if xs == [] then
    []
  else
    [xs[0]] + [xs[0]] + Dup(xs[1..])
}

function DupRev<A>(xs: seq<A>): seq<A>
  ensures 2*|xs| == |DupRev(xs)|
{
  if xs == [] then
    []
  else
    DupRev(xs[..|xs|-1]) + [xs[|xs|-1]] + [xs[|xs|-1]]
}

lemma DupDupRev<A>(xs: seq<A>)
  ensures Dup(xs) == DupRev(xs)
// {
//   if xs == [] {
//   } else {
//     calc == {
//       Dup(xs);
//       [xs[0]] + [xs[0]] + Dup(xs[1..]);
//       DupRev(xs[..|xs|-1]) + [xs[|xs|-1]] + [xs[|xs|-1]];
//       DupRev(xs);
//     }
//   }
// }

method DupElements(l: LinkedList)
  modifies l, l.Repr()
  requires l.Valid()
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures l.Model() == old(Dup(l.Model()))
  ensures forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() :: allocated(x)
{
  var it := l.Begin();
  ghost var i := 0;
  while it.HasNext()
    decreases |l.Model()| - it.Index()
    invariant l.Valid()
    invariant 2*i <= |l.Model()|
    invariant i <= old(|l.Model()|)
    invariant l.Model()[..2*i] == old(DupRev(l.Model()[..i]))
    invariant l.Model()[2*i..] == old(l.Model()[i..])
    invariant it.Parent() == l
    invariant it.Valid()
    invariant {it} !! {l}
    invariant it.Index() == 2*i
    invariant it in l.Iterators()
    invariant forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
    invariant forall x | x in l.Repr() :: allocated(x)
  {
    assert i < old(|l.Model()|);
    ghost var omodel := l.Model();
    assert omodel[..2*i] == old(DupRev(l.Model()[..i]));
    var x := it.Peek();
    l.Insert(it, x);
    ghost var model := l.Model();
    calc == {
      model;
      Seq.Insert(x, omodel, it.Index());
      omodel[..it.Index()+1] + [x] + omodel[it.Index()+1..];
      omodel[..2*i+1] + [x] + omodel[2*i+1..];
      omodel[..2*i] + [x] + [x] + omodel[2*i+1..];
      old(DupRev(l.Model()[..i])) + [x] + [x] + omodel[2*i+1..];
      { assert old(l.Model()[i]) == x; }
      old(DupRev(l.Model()[..i])) + [old(l.Model()[i])] + [old(l.Model()[i])] + omodel[2*i+1..];
      { assert old(l.Model()[..i+1][..|l.Model()[..i+1]|-1]) == old(l.Model()[..i]); }
      old(DupRev(l.Model()[..i+1])) + omodel[2*i+1..];
    }
    assert model == old(DupRev(l.Model()[..i+1])) + omodel[2*i+1..];
    x := it.Next();
    x := it.Next();
    i := i + 1;
  }
  calc == {
    l.Model();
    l.Model()[..2*i];
    old(DupRev(l.Model()[..i]));
    { assert old(l.Model()[..i]) == old(l.Model()); }
    old(DupRev(l.Model()));
    { DupDupRev(old(l.Model())); }
    old(Dup(l.Model()));
  }
  assert l.Model() == old(Dup(l.Model()));
}

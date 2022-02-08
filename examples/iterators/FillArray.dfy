include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"

method  FillArray(l: List, v: array<int>)
  modifies l,l.Repr(), v
  requires {v} !! {l}+l.Repr()
  requires l.Valid()
  requires v.Length == |l.Model()|
  requires forall x | x in l.Repr() :: allocated(x)

  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures v[..] == l.Model()

  ensures l.Iterators() >= old(l.Iterators())

  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)
  ensures {v} !! {l} + l.Repr()
{
  var it := l.Begin();

  var i := 0;
  while it.HasNext()
    decreases |l.Model()| - it.Index()
    invariant l.Valid()
    invariant l.Model() == old(l.Model())
    invariant it.Parent() == l
    invariant it.Valid()
    //invariant {it} !! {l}
    invariant {v}!! {l}
    invariant {v} !! l.Repr()
    //invariant {v} !! {it}
    invariant it.Index() == i
    invariant i <= |l.Model()|
    invariant v[..i] == l.Model()[..i]

    invariant l.Iterators() >= old(l.Iterators())

    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant forall x | x in l.Repr() :: allocated(x)
  {
    var x := it.Next();
    v[i] := x;
    i := i + 1;
  }
}

method  FillArrayLL(l: LinkedList, v: array<int>)
  modifies l, l.Repr(), v
  requires {v} !! {l}
  requires {v} !! l.Repr()
  requires l.Valid()
  requires v.Length == |l.Model()|
  requires forall x | x in l.Repr() :: allocated(x)

  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures v[..] == l.Model()

  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) :: it.Valid() && it.Index()==old(it.Index())

  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)
  ensures {v} !! {l} + l.Repr()
{
  ghost var iters:=l.Iterators();
  var it := l.Begin();

  var i := 0;
  while it.HasNext()
    decreases |l.Model()| - it.Index()
    invariant l.Valid()
    invariant l.Model() == old(l.Model())
    invariant it.Parent() == l
    invariant it.Valid()
    //invariant {it} !! {l}
    invariant {v}!! {l}
    invariant {v} !! l.Repr()
    //invariant {v} !! {it}
    invariant it.Index() == i
    invariant i <= |l.Model()|
    invariant v[..i] == l.Model()[..i]

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) :: it.Valid() && it.Index()==old(it.Index())

    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant forall x | x in l.Repr() :: allocated(x)
  {

    var x := it.Next();
    v[i] := x;
    i := i + 1;
  }
}

method  FillArrayAL(l: ArrayList, v: array<int>)
  modifies l, l.Repr(), v
  requires {v} !! {l}
  requires {v} !! l.Repr()
  requires l.Valid()
  requires v.Length == |l.Model()|
  requires forall x | x in l.Repr() :: allocated(x)

  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures v[..] == l.Model()

  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) :: it.Valid() && it.Index()==old(it.Index())

  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)
  ensures {v} !! {l} + l.Repr()
{
  ghost var iters := l.Iterators();
  var it := l.Begin();

  var i := 0;
  while it.HasNext()
    decreases |l.Model()| - it.Index()
    invariant l.Valid()
    invariant l.Model() == old(l.Model())
    invariant it.Parent() == l
    invariant it.Valid()
    invariant {it} !! {l}
    invariant {v}!! {l}
    invariant {v} !! l.Repr()
    invariant {v} !! {it}
    invariant it.Index() == i
    invariant i <= |l.Model()|
    invariant v[..i] == l.Model()[..i]

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) :: it.Valid() && it.Index()==old(it.Index())

    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant forall x | x in l.Repr() :: allocated(x)
  {
    var x := it.Next();
    v[i] := x;
    i := i + 1;
  }
}

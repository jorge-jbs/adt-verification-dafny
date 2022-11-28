include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"

method FillArray<A>(l: List<A>, v: array<A>)
  modifies l,l.Repr(), v
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires l.Valid()
  requires {v} !! {l}+l.Repr()
  requires v.Length == |l.Model()|

  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures v[..] == l.Model()
  ensures {v} !! {l} + l.Repr()

  ensures l.Iterators() >= old(l.Iterators())

{
  var it := l.Begin();
  var b := it.HasNext();

  var i := 0;
  while b
    decreases |l.Model()| - it.Index()
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant allocated(l.Repr())

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
    invariant b == it.HasNext?()

    invariant l.Iterators() >= old(l.Iterators())
  {
    var x := it.Next();
    v[i] := x;
    b := it.HasNext();
    i := i + 1;
  }
}

method FillArrayLL<A>(l: LinkedList<A>, v: array<A>)
  modifies l, l.Repr(), v
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires {v} !! {l}
  requires {v} !! l.Repr()
  requires l.Valid()
  requires v.Length == |l.Model()|

  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures v[..] == l.Model()
  ensures {v} !! {l} + l.Repr()

  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) :: it.Valid() && it.Parent()==old(it.Parent()) && it.Index()==old(it.Index())
{
  ghost var iters:=l.Iterators();
  var it := l.Begin();
  var b := it.HasNext();

  var i := 0;
  while b
    decreases |l.Model()| - it.Index()
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant allocated(l.Repr())

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
    invariant b == it.HasNext?()

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) :: it.Valid() && it.Parent()==old(it.Parent()) && it.Index()==old(it.Index())
  {

    var x := it.Next();
    v[i] := x;
    b := it.HasNext();
    i := i + 1;
  }
}

method FillArrayAL<A>(l: ArrayList<A>, v: array<A>)
  modifies l, l.Repr(), v
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires l.Valid()
  requires {v} !! {l}
  requires {v} !! l.Repr()
  requires v.Length == |l.Model()|

  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures v[..] == l.Model()
  ensures {v} !! {l} + l.Repr()

  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) :: it.Valid() && it.Parent()==old(it.Parent()) && it.Index()==old(it.Index())
{
  ghost var iters := l.Iterators();
  var it := l.Begin();
  var b := it.HasNext();

  var i := 0;
  while b
    decreases |l.Model()| - it.Index()
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant allocated(l.Repr())

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
    invariant b == it.HasNext?()

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) :: it.Valid() && it.Parent()==old(it.Parent()) && it.Index()==old(it.Index())
  {
    var x := it.Next();
    v[i] := x;
    b := it.HasNext();
    i := i + 1;
  }
}

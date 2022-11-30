include "../../src/linear/layer1/List.dfy"
//include "../../src/linear/layer2/LinkedList.dfy"
//include "../../src/linear/layer2/ArrayList.dfy"


method FillArray<A>(l: List<A>, v: array<A>)
  modifies l,l.Repr(), v
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires ValidDistinct([l],[v])
  requires v.Length == |l.Model()|

  ensures ValidDistinct([l],[v])
  ensures l.Model() == old(l.Model())
  ensures v[..] == l.Model()

  ensures l.Iterators() >= old(l.Iterators())

{
  var it := l.First();
  var b := it.HasPeek();

  var i := 0;
  while b
    decreases |l.Model()| - it.Index()
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant allocated(l.Repr())

    invariant l.Valid()
    invariant l.Model() == old(l.Model())
    invariant it.Parent() == l
    invariant it.Valid()
    invariant  ValidDistinct([l],[v])
    invariant {v} !! {it}
    invariant it.Index() == i
    invariant i <= |l.Model()|
    invariant v[..i] == l.Model()[..i]
    invariant b == it.HasPeek?()

    invariant l.Iterators() >= old(l.Iterators())
  {
    v[i] := it.Peek();
    it.Next();
    b := it.HasPeek();
    i := i + 1;
  }
}


method FillArrayBack<A>(l: List<A>, v: array<A>)
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
  var it := l.Last();
  assert it.Index()==|l.Model()|-1;
  var b := it.HasPeek();

  var i := l.Size();
  i:= i - 1;

  while b
    decreases it.Index()
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant allocated(l.Repr())

    invariant l.Valid()
    invariant l.Model() == old(l.Model())
    invariant it.Parent() == l
    invariant it.Valid()
    invariant {v} !! {l}
    invariant {v} !! l.Repr()
    invariant it.Index() == i
    invariant -1 <= i < |l.Model()|
    invariant v[i+1..] == l.Model()[i+1..]
    invariant b == it.HasPeek?()

    invariant l.Iterators() >= old(l.Iterators())
  {
    v[i] := it.Peek();
    it.Prev();
    b := it.HasPeek();
    i := i - 1;
  }
}
/*method FillArrayLL<A>(l: LinkedList<A>, v: array<A>)
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
    invariant {v} !! {l}
    invariant {v} !! l.Repr()
    //invariant {v} !! {it}
    invariant it.Index() == i
    invariant i <= |l.Model()|
    invariant v[..i] == l.Model()[..i]
    invariant b == it.HasNext?()

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) :: it.Valid() && it.Parent()==old(it.Parent()) && it.Index()==old(it.Index())
  {

    var x := it.Peek();
    v[i] := x;
    it.Next();
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
    var x := it.Peek();
    v[i] := x;
    it.Next();
    b := it.HasNext();
    i := i + 1;
  }
}*/

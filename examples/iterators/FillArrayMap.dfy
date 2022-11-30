include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"
include "../../src/Iterators_Utils.dfy"

method FillArrayLL<A>(l: LinkedList<A>, v: array<A>) returns (ghost mit:map<int,int>)
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

  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && it.Parent()==old(it.Parent()) && mit[old(it.Index())]==it.Index()
  ensures mit==identityMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())))
  //ensures mit==buildMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),identity)
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()):: old(it.Index()) in mit //domain
  ensures forall i | i in mit :: mit[i]==identity(i) //range
  ensures {v} !! {l} + l.Repr()
{
  var validSet:=set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index());
  mit:=identityMap(validSet);

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
    invariant {v} !! {l}
    invariant {v} !! l.Repr()
    invariant {v} !! {it}
    invariant it.Index() == i
    invariant i <= |l.Model()|
    invariant v[..i] == l.Model()[..i]
    invariant b == it.HasNext?()

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && it.Parent()==old(it.Parent()) && mit[old(it.Index())]==it.Index();
  {
    var x := it.Next();
    v[i] := x;
    b := it.HasNext();
    i := i + 1;
  }
}

method FillArrayAL<A>(l: ArrayList<A>, v: array<A>)returns (ghost mit:map<int,int>)
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

  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && it.Parent()==old(it.Parent()) && mit[old(it.Index())]==it.Index()
  ensures mit==identityMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())))
  //ensures mit==buildMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),identity)
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()):: old(it.Index()) in mit //domain
  ensures forall i | i in mit :: mit[i]==identity(i) //range
  ensures {v} !! {l} + l.Repr()
{
  var validSet:=set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index());
  mit:=identityMap(validSet);

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
    invariant {v} !! {l}
    invariant {v} !! l.Repr()
    invariant {v} !! {it}
    invariant it.Index() == i
    invariant i <= |l.Model()|
    invariant v[..i] == l.Model()[..i]
    invariant b == it.HasNext?()

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && it.Parent()==old(it.Parent()) && mit[old(it.Index())]==it.Index();
  {
    var x := it.Next();
    v[i] := x;
    b := it.HasNext();
    i := i + 1;
  }
}

include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"
include "../../src/Iterators_Utils.dfy"

method FillArrayLL<A>(l: LinkedList<A>, v: array<A>) returns (ghost mit:map<int,int>)
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
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && mit[old(it.Index())]==it.Index()
  ensures mit==identityMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())))
  //ensures mit==buildMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),identity)
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()):: old(it.Index()) in mit //domain
  ensures forall i | i in mit :: mit[i]==identity(i) //range

  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)
  ensures {v} !! {l} + l.Repr()
{
  var validSet:=set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index());
  mit:=identityMap(validSet);

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
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && mit[old(it.Index())]==it.Index();

    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant forall x | x in l.Repr() :: allocated(x)
  {
    var x := it.Next();
    v[i] := x;
    i := i + 1;
  }
}

method FillArrayAL<A>(l: ArrayList<A>, v: array<A>)returns (ghost mit:map<int,int>)
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
  ensures mit==identityMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())))
  //ensures mit==buildMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),identity)
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()):: old(it.Index()) in mit //domain
  ensures forall i | i in mit :: mit[i]==identity(i) //range

  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)
  ensures {v} !! {l} + l.Repr()
{
  var validSet:=set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index());
  mit:=identityMap(validSet);

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
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && mit[old(it.Index())]==it.Index();

    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant forall x | x in l.Repr() :: allocated(x)
  {
    var x := it.Next();
    v[i] := x;
    i := i + 1;
  }
}

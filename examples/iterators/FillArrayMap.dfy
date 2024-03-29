include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"
include "../../src/Iterators_Utils.dfy"

method FillArrayLL<A>(l: LinkedList<A>, v: array<A>) returns (ghost mit:map<int,int>)
  modifies l, l.Repr(), v
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires l.Valid()
  requires {v} !! {l} + l.Repr()
  requires v.Length == |l.Model()|

  ensures l.Valid()
  ensures {v} !! {l} + l.Repr()
  ensures l.Model() == old(l.Model())
  ensures v[..] == l.Model()

  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::
     it.Valid() && it.Parent() == old(it.Parent()) && mit[old(it.Index())] == it.Index()
  ensures mit == IdentityMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())))
  //ensures mit==BuildMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),Identity)
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()):: old(it.Index()) in mit //domain
  ensures forall i | i in mit :: mit[i] == Identity(i) //range
{
  var validSet := set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index());
  mit := IdentityMap(validSet);

  var it := l.First();
  var b := it.HasPeek();

  var i := 0;
  while b
    decreases |l.Model()| - it.Index()
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant allocated(l.Repr())

    invariant l.Valid()
    invariant {v} !! {l} + l.Repr()
    invariant l.Model() == old(l.Model())
    invariant it.Parent() == l
    invariant it.Valid()
    invariant it.Index() == i
    invariant i <= |l.Model()|
    invariant v[..i] == l.Model()[..i]
    invariant b == it.HasPeek?()

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::
       it.Valid() && it.Parent() == old(it.Parent()) && mit[old(it.Index())] == it.Index();
  {
    var x := it.Peek();
    it.Next();
    v[i] := x;
    b := it.HasPeek();
    i := i + 1;
  }
}

method FillArrayAL<A>(l: ArrayList<A>, v: array<A>)returns (ghost mit:map<int,int>)
  modifies l, l.Repr(), v
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires l.Valid()
  requires {v} !! {l} + l.Repr()
  requires v.Length == |l.Model()|

  ensures l.Valid()
  ensures {v} !! {l} + l.Repr()
  ensures l.Model() == old(l.Model())
  ensures v[..] == l.Model()

  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::
     it.Valid() && it.Parent() == old(it.Parent()) && mit[old(it.Index())]==it.Index()
  ensures mit == IdentityMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())))
  //ensures mit==BuildMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),Identity)
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()):: old(it.Index()) in mit //domain
  ensures forall i | i in mit :: mit[i] == Identity(i) //range
{
  var validSet:=set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index());
  mit:=IdentityMap(validSet);

  var it := l.First();
  var b := it.HasPeek();

  var i := 0;

  while b 
    decreases |l.Model()| - it.Index()
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant allocated(l.Repr())

    invariant l.Valid()
    invariant {v} !! {l} + l.Repr()
    invariant l.Model() == old(l.Model())
    invariant it.Parent() == l
    invariant it.Valid()
    invariant it.Index() == i
    invariant i <= |l.Model()|
    invariant v[..i] == l.Model()[..i]
    invariant b == it.HasPeek?()

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::
       it.Valid() && it.Parent() == old(it.Parent()) && mit[old(it.Index())] == it.Index();
  {
    var x := it.Peek();
    v[i] := x;
    it.Next();
    b := it.HasPeek();
    i := i + 1;
  }
}

include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"


method AllProperty<A>(l: List<A>, p:A -> bool) returns (b:bool)
  modifies l,l.Repr()
  requires l.Valid()
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures b == forall i | 0 <= i < |old(l.Model())| :: p(old(l.Model())[i]) 

  ensures l.Iterators() >= old(l.Iterators())
{
  var it := l.First();
  var itHasPeek := it.HasPeek();
  b:=true; 

  while (itHasPeek && b)
  decreases |l.Model()|-it.Index()
  invariant allocated(l.Repr())
  invariant fresh(l.Repr()-old(l.Repr()))

  invariant l.Valid() && it.Valid() && it.Parent() == l && it in l.Iterators()
  invariant l.Model() == old(l.Model())
  invariant 0 <= it.Index() <= |old(l.Model())|
  invariant b == (forall i | 0 <= i < it.Index() :: p(old(l.Model())[i]))
  invariant itHasPeek == it.HasPeek?()

  invariant  l.Iterators() >= old(l.Iterators())
  {  var itPeek := it.Peek();
     it.Next();
     b := p(itPeek);
     itHasPeek := it.HasPeek();
  }
}


method AllPositive(l: List<int>) returns (b:bool)
  modifies l,l.Repr()
  requires l.Valid()
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures b == forall i | 0 <= i < |old(l.Model())| :: old(l.Model())[i] >= 0

  ensures l.Iterators() >= old(l.Iterators())
{ b := AllProperty(l, x => x >= 0);} 


method AllEven(l: List<int>) returns (b:bool)
  modifies l,l.Repr()
  requires l.Valid()
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures b == forall i | 0 <= i < |old(l.Model())| :: old(l.Model())[i]%2 == 0 

  ensures l.Iterators() >= old(l.Iterators())
{ b := AllProperty(l, x => x%2 == 0);} 
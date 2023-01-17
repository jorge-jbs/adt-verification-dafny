include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"
include "../../src/OrderCloseEnded.dfy"

method AllRelated<A>(l: List<A>, r: (A,A) -> bool) returns (b:bool)
  modifies l,l.Repr()
  requires l.Valid()
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires IsPreorder(r,set x | x in l.Model())//reflexive and transitive

  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures b == forall i,j | 0 <= i <= j < |old(l.Model())| :: r(old(l.Model())[i], old(l.Model())[j]) 

  ensures l.Iterators() >= old(l.Iterators())
{
  var it := l.First();
  var prev := l.First();  
  var itHasPeek := it.HasPeek();
  if (itHasPeek) { it.Next(); }
  itHasPeek := it.HasPeek();
  b:=true; 

  while (itHasPeek && b)
  decreases |l.Model()|-it.Index()
  invariant allocated(l.Repr())
  invariant fresh(l.Repr()-old(l.Repr()))

  invariant l.Valid() && it.Valid() && it.Parent() == l && it in l.Iterators()
  invariant prev.Valid() && prev.Parent() == l && prev in l.Iterators()
  invariant l.Model() == old(l.Model())
  invariant 0 <= it.Index() <= |old(l.Model())|
  invariant itHasPeek ==> 0 <= prev.Index() == it.Index()-1
  invariant b == (forall i,j | 0 <= i <= j < it.Index() :: r(old(l.Model())[i], old(l.Model())[j]))
  invariant itHasPeek == it.HasPeek?()

  invariant  l.Iterators() >= old(l.Iterators())
  {  var itPeek := it.Peek();
     var prevPeek := prev.Peek();
     prev.Next();
     it.Next();
     b := r(prevPeek,itPeek);
     itHasPeek := it.HasPeek();
  }
}

method AllEqual<A(==)>(l: List<A>) returns (b:bool)
  modifies l,l.Repr()
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires l.Valid()
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures b == forall i, j | 0 <= i <= j < |old(l.Model())| :: old(l.Model())[i] == old(l.Model())[j]
  
  ensures l.Iterators() >= old(l.Iterators())
{ b := AllRelated(l, (x,y) => x==y); } 


method Sorted<A>(l: List<A>, le:(A,A) -> bool) returns (b:bool)
  modifies l,l.Repr()
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())


  requires l.Valid()
  requires IsTotalOrder(le,set x | x in l.Model())
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures b == forall i, j | 0 <= i <= j < |old(l.Model())| :: le(old(l.Model())[i],old(l.Model())[j])
  
  ensures l.Iterators() >= old(l.Iterators())
{ b := AllRelated(l, (x,y) => le(x,y)); } 


method DecSorted(l: List<int>) returns (b:bool)
  modifies l,l.Repr()
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires l.Valid()
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures b == forall i, j | 0 <= i <= j < |old(l.Model())| :: old(l.Model())[i] >= old(l.Model())[j]

  ensures l.Iterators() >= old(l.Iterators())
{ 
  b := AllRelated(l, (x,y) => x >= y); 
} 

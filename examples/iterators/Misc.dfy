include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"

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
{
  var it := l.Begin();
  var itHasNext := it.HasNext();
  b:=true; 

  while (itHasNext && b)
  decreases |l.Model()|-it.Index()
  invariant allocated(l.Repr())
  invariant fresh(l.Repr()-old(l.Repr()))

  invariant l.Valid() && it.Valid() && it.Parent()==l && it in l.Iterators()
  invariant l.Model()==old(l.Model())
  invariant 0 <= it.Index() <= |old(l.Model())|
  invariant b == (forall i | 0 <= i < it.Index() :: old(l.Model())[i]>=0)
  invariant itHasNext == it.HasNext?()

  invariant  l.Iterators() >= old(l.Iterators())
  {  var itPeek := it.Next();
     b := itPeek >= 0;
     itHasNext := it.HasNext();
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
  ensures b == forall i| 0 <= i < |old(l.Model())|-1 :: old(l.Model())[i]==old(l.Model())[i+1]
  
  ensures l.Iterators() >= old(l.Iterators())
{
  var it1 := l.Begin();
  var it2 := l.Begin();
  var it1HasNext := it1.HasNext();
  if it1HasNext {
    var _ := it1.Next();
  }
  it1HasNext := it1.HasNext();
  b:=true;

  while (it1HasNext && b)
    decreases |l.Model()|-it1.Index()
    invariant allocated(l.Repr())
    invariant fresh(l.Repr()-old(l.Repr()))

    invariant l.Valid() && it1.Valid() && it1.Parent()==l && it1 in l.Iterators()
    invariant it2.Valid() && it2.Parent()==l && it2 in l.Iterators()
    invariant l.Model()==old(l.Model())
    invariant 0 <= it1.Index() <= |old(l.Model())|
    invariant it2.HasNext?() ==> it2.Index()==it1.Index()-1
    invariant it1.HasNext?() ==> it2.HasNext?()
    invariant b == (forall i | 0 <= i < it1.Index()-1:: old(l.Model())[i]==old(l.Model())[i+1])
    invariant it1HasNext == it1.HasNext?()

    invariant l.Iterators() >= old(l.Iterators())
  {
    var it2Peek := it2.Next();
    var it1Peek := it1.Next();
    b := it1Peek == it2Peek;
    it1HasNext := it1.HasNext();
  }
}

method IteratorExample2(l: List<int>)
modifies l, l.Repr()
requires allocated(l.Repr())
ensures fresh(l.Repr()-old(l.Repr()))
ensures allocated(l.Repr())

requires l.Valid()
requires l.Model() != []
requires forall x | x in l.Repr() :: allocated(x)
ensures l.Valid()
ensures l.Model() == old(l.Model())
{

  var it1 := l.Begin();
  var it2 := l.Begin();
}

method IteratorExample3(l: LinkedList<int>)
modifies l, l.Repr()
requires allocated(l.Repr())
ensures fresh(l.Repr()-old(l.Repr()))
ensures allocated(l.Repr())

requires l.Valid()
requires l.Model() != []
ensures l.Valid()
{
  var it1 := l.Begin();
  var it2 := l.Begin();
  var x := it2.Next();
  var y := l.PopFront();
  assert x == y;
  //assert !it1.Valid();  // we cannot prove nor disprove this assertion
  assert it2.Valid();
}
method  IteratorExample4(l: List<int>)
modifies l, l.Repr()
requires allocated(l.Repr())
ensures fresh(l.Repr()-old(l.Repr()))
ensures allocated(l.Repr())
requires l.Valid()
ensures l.Valid()
{
  var it1 := l.Begin();
  var it2 := l.Begin();
  it1:=l.Insert(it1,2);it1:=l.Insert(it1,2);
  var b:=it1.HasNext();
  if b {it1:=l.Erase(it1);it1:=l.Insert(it1,4);}
}
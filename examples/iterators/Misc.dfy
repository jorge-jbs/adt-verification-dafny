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
  var it := l.First();
  var itHasPeek := it.HasPeek();
  b := true;

  while (itHasPeek && b)
    decreases |l.Model()|-it.Index()
    invariant allocated(l.Repr())
    invariant fresh(l.Repr()-old(l.Repr()))

    invariant l.Valid() && it.Valid() && it.Parent()==l && it in l.Iterators()
    invariant l.Model()==old(l.Model())
    invariant 0 <= it.Index() <= |old(l.Model())|
    invariant b == (forall i | 0 <= i < it.Index() :: old(l.Model())[i]>=0)
    invariant itHasPeek == it.HasPeek?()

    invariant  l.Iterators() >= old(l.Iterators())
  {
    var itPeek := it.Peek();
    it.Next();
    b := itPeek >= 0;
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
  ensures b == forall i| 0 <= i < |old(l.Model())|-1 :: old(l.Model())[i]==old(l.Model())[i+1]

  ensures l.Iterators() >= old(l.Iterators())
{
  var it1 := l.First();
  var it2 := l.First();
  var it1HasPeek := it1.HasPeek();
  if it1HasPeek {
    it1.Next();
  }
  it1HasPeek := it1.HasPeek();
  b := true;

  while it1HasPeek && b
    decreases |l.Model()|-it1.Index()
    invariant allocated(l.Repr())
    invariant fresh(l.Repr()-old(l.Repr()))

    invariant l.Valid() && it1.Valid() && it1.Parent()==l && it1 in l.Iterators()
    invariant it2.Valid() && it2.Parent()==l && it2 in l.Iterators()
    invariant l.Model()==old(l.Model())
    invariant 0 <= it1.Index() <= |old(l.Model())|
    invariant it2.HasPeek?() ==> it2.Index()==it1.Index()-1
    invariant it1.HasPeek?() ==> it2.HasPeek?()
    invariant b == (forall i | 0 <= i < it1.Index()-1:: old(l.Model())[i]==old(l.Model())[i+1])
    invariant it1HasPeek == it1.HasPeek?()

    invariant l.Iterators() >= old(l.Iterators())
  {
    var it2Peek := it2.Peek();
    it2.Next();
    var it1Peek := it1.Peek();
    it1.Next();
    b := it1Peek == it2Peek;
    it1HasPeek := it1.HasPeek();
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

  var it1 := l.First();
  var it2 := l.First();
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
  var it1 := l.First();
  var it2 := l.First();
  var x := it2.Peek();
  it2.Next();
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
  var it1 := l.First();
  var it2 := l.First();
  it1 := l.Insert(it1, 2);
  it1 := l.Insert(it1, 2);
  var b := it1.HasPeek();
  if b {
    it1 := l.Erase(it1);
    it1 := l.Insert(it1, 4);
  }
}
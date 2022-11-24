include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"

method FindMax(l: LinkedList<int>) returns (max: ListIterator<int>)
  modifies l, l.Repr()
  requires allocated(l.Repr())

  requires l.Valid()
  requires l.Model() != []
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures fresh(max) && max in l.Iterators()
  ensures max.Valid()
  ensures max.Parent() == l
  ensures max.HasNext?()
  ensures forall x | x in l.Model() :: l.Model()[max.Index()] >= x

  ensures fresh(l.Repr() - old(l.Repr()))
  ensures allocated(l.Repr())

  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) ::
    it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())

{
  max := l.Begin();
  var it := l.Begin();
  var b := it.HasNext(); //Nuevo

  while b
    decreases |l.Model()| - it.Index()
    invariant l.Valid()
    invariant l.Model() == old(l.Model())
    invariant it.Valid()
    invariant it in l.Iterators()
    invariant fresh(max)
    invariant max.Valid()
    invariant max.Parent() == l
    invariant max in l.Iterators()
    invariant max != it
    invariant max.HasNext?()
    invariant it.Index() <= |l.Model()|
    invariant forall k | 0 <= k < it.Index() :: l.Model()[max.Index()] >= l.Model()[k]
    invariant b == it.HasNext?()

    invariant allocated(l.Repr())
    invariant fresh(l.Repr() - old(l.Repr()))

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())

  { var itPeek := it.Peek(); 
    var maxPeek := max.Peek();

    if itPeek > maxPeek {
      max := it.Copy();
    }
    var _ := it.Next();
    b := it.HasNext();
  }
}


method FindMaxAL(l: ArrayList<int>) returns (max: ListIterator<int>)
  modifies l, l.Repr()
  requires allocated(l.Repr())

  requires l.Valid()
  requires l.Model() != []
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures fresh(max) && max in l.Iterators()
  ensures max.Valid()
  ensures max.Parent() == l
  ensures max.HasNext?()
  ensures forall x | x in l.Model() :: l.Model()[max.Index()] >= x

  ensures fresh(l.Repr() - old(l.Repr()))
  ensures allocated(l.Repr())

  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) ::
    it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())

{
  max := l.Begin();
  var it := l.Begin();
  var b := it.HasNext();

  while b
    decreases |l.Model()| - it.Index()
    invariant l.Valid()
    invariant l.Model() == old(l.Model())
    invariant it.Valid()
    invariant it.Parent() == l
    invariant it in l.Iterators()
    invariant fresh(max)
    invariant max.Valid()
    invariant max.Parent() == l
    invariant max in l.Iterators()
    invariant max != it
    invariant max.HasNext?()
    invariant it.Index() <= |l.Model()|
    invariant forall k | 0 <= k < it.Index() :: l.Model()[max.Index()] >= l.Model()[k]
    invariant b == it.HasNext?()
    
    invariant allocated(l.Repr())
    invariant fresh(l.Repr() - old(l.Repr()))

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())
  {
    var itPeek := it.Peek(); 
    var maxPeek := max.Peek();

    if itPeek > maxPeek {
      max := it.Copy();
    }
    var _ := it.Next();
    
    b := it.HasNext();
  }
}


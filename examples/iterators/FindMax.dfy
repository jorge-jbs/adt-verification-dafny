include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"

method FindMax(l: LinkedList<int>) returns (max: ListIterator<int>)
  modifies l, l.Repr()
  requires l.Valid()
  requires l.Model() != []
  requires forall x | x in l.Repr() :: allocated(x)
  
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures fresh(max) && max in l.Iterators()
  ensures max.Valid()
  ensures max.Parent() == l
  ensures max.HasNext()
  ensures forall x | x in l.Model() :: l.Model()[max.Index()] >= x

  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) ::
    it.Valid() && it.Index() == old(it.Index())

  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() :: allocated(x)

{
  max := l.Begin();
  var it := l.Begin();
  while it.HasNext()
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
    invariant max.HasNext()
    invariant it.Index() <= |l.Model()|
    invariant forall k | 0 <= k < it.Index() :: l.Model()[max.Index()] >= l.Model()[k]
    
    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())

    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
    invariant forall x | x in l.Repr() :: allocated(x)
    invariant forall x | x in old(l.Repr()) :: allocated(x)  
  {
    if it.Peek() > max.Peek() {
      max := it.Copy();
    }
    var x := it.Next();
  }
}

method FindMaxAL(l: ArrayList<int>) returns (max: ListIterator<int>)
  modifies l, l.Repr()
  requires l.Valid()
  requires l.Model() != []
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures fresh(max) && max in l.Iterators()
  ensures max.Valid()
  ensures max.Parent() == l
  ensures max.HasNext()
  ensures forall x | x in l.Model() :: l.Model()[max.Index()] >= x

  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) ::
    it.Valid() && it.Index() == old(it.Index())

  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() :: allocated(x)  
{
  max := l.Begin();
  var it := l.Begin();
  while it.HasNext()
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
    invariant max.HasNext()
    invariant it.Index() <= |l.Model()|
    invariant forall k | 0 <= k < it.Index() :: l.Model()[max.Index()] >= l.Model()[k]
    
    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())

    invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
    invariant forall x | x in l.Repr() :: allocated(x)
    invariant forall x | x in old(l.Repr()) :: allocated(x)  
  {
    if it.Peek() > max.Peek() {
      max := it.Copy();
    }
    var x := it.Next();
  }
}

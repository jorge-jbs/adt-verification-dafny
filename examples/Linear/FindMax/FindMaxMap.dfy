include "../../../src/List/ListSpec.dfy"
include "../../../src/LinkedList/LinkedListSpec.dfy"
include "../../../src/ArrayList/ArrayListSpec.dfy"
include "../../../src/Collections/Map.dfy"


module FindMaxMap{
  import opened ListSpec
  import opened LinkedListSpec
  import opened ArrayListSpec
  import opened Map
  
  export provides ListSpec, LinkedListSpec, ArrayListSpec, Map
         provides FindMax, FindMaxAL

method FindMax(l: LinkedList<int>) returns (max: ListIterator<int>, ghost mit:map<int,int>)
  modifies l, l.Repr()
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires l.Valid()
  requires l.Model() != []
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures fresh(max) && max in l.Iterators()
  ensures max.Valid()
  ensures max.Parent() == l
  ensures max.HasPeek?()
  ensures forall x | x in l.Model() :: l.Model()[max.Index()] >= x
  
  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::
    && it.Valid() 
    && it.Parent() == old(it.Parent()) 
    && mit[old(it.Index())] == it.Index()
  
  ensures mit == IdSeqMap(old(l.Model()))
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()):: old(it.Index()) in mit //domain
  ensures forall i | i in mit :: mit[i] == i //range  
{
  mit := map it | -1 <= it <= |old(l.Model())|::it;

  max := l.First();
  var it := l.First();
  var b := it.HasPeek();

  while b
    decreases |l.Model()| - it.Index()
    invariant allocated(l.Repr())
    invariant fresh(l.Repr()-old(l.Repr()))

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
    invariant max.HasPeek?()
    invariant it.Index() <= |l.Model()|
    invariant forall k | 0 <= k < it.Index() :: l.Model()[max.Index()] >= l.Model()[k]
    invariant b == it.HasPeek?()
    
    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && mit[old(it.Index())] == it.Index() 
  {
    var itPeek := it.Peek(); 
    var maxPeek := max.Peek();

    if itPeek > maxPeek {
      max := it.Copy();
    }
    it.Next();
    b := it.HasPeek();
  }
}


method FindMaxAL(l: ArrayList<int>) returns (max: ListIterator<int>, ghost mit:map<int,int>)
  modifies l, l.Repr()
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires l.Valid()
  requires l.Model() != []
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures fresh(max) && max in l.Iterators()
  ensures max.Valid()
  ensures max.Parent() == l
  ensures max.HasPeek?()
  ensures forall x | x in l.Model() :: l.Model()[max.Index()] >= x
  
  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::
    && it.Valid() 
    && it.Parent() == old(it.Parent()) 
    && mit[old(it.Index())] == it.Index()
  
  ensures mit == BuildMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),Identity)
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()):: old(it.Index()) in mit //domain
  ensures forall i | i in mit :: mit[i] == Identity(i) //range
{
    var setValid:=set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index());
    mit:=BuildMap(setValid,Identity);


  max := l.First();
  var it := l.First();
  var b := it.HasPeek();

  while b
    decreases |l.Model()| - it.Index()
    invariant allocated(l.Repr())
    invariant fresh(l.Repr()-old(l.Repr()))

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
    invariant max.HasPeek?()
    invariant it.Index() <= |l.Model()|
    invariant forall k | 0 <= k < it.Index() :: l.Model()[max.Index()] >= l.Model()[k]
    invariant b == it.HasPeek?()

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::
     && it.Valid() 
     && it.Parent() == old(it.Parent()) 
     && mit[old(it.Index())] == it.Index()    
  {
    var itPeek := it.Peek(); 
    var maxPeek := max.Peek();

    if itPeek > maxPeek {
      max := it.Copy();
    }
    it.Next();
    b := it.HasPeek();
  }
}
}
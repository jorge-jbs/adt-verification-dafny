include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"
include "../../src/Iterators_Utils.dfy"

function idMap(xs:seq<int>):map<int,int>
{map i | 0<=i<=|xs| :: i}

method FindMax(l: LinkedList) returns (max: ListIterator,ghost mit:map<int,int>)
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
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && mit[old(it.Index())]==it.Index()
  ensures mit==idMap(old(l.Model()))
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()):: old(it.Index()) in mit //domain
  ensures forall i | i in mit :: mit[i]==i //range

  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() :: allocated(x)
  
{
   mit:= map it | 0<=it<=|old(l.Model())|::it;


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
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && mit[old(it.Index())]==it.Index();

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


method FindMaxAL(l: ArrayList) returns (max: ListIterator, ghost mit:map<int,int>)
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
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && mit[old(it.Index())]==it.Index()
  ensures mit==buildMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),identity)
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()):: old(it.Index()) in mit //domain
  ensures forall i | i in mit :: mit[i]==identity(i) //range


  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
  ensures forall x | x in l.Repr() :: allocated(x)  
{
    var setValid:=set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index());
    mit:=buildMap(setValid,identity);


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
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::it.Valid() && mit[old(it.Index())]==it.Index();

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

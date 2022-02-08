include "../../src/linear/adt/List.dfy"
include "../../src/linear/impl/LinkedList.dfy"
include "../../src/linear/impl/VectorImpl.dfy"

method  allPositive(l: List) returns (b:bool)
  modifies l,l.Repr()
  requires l.Valid()
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures b== forall i| 0<=i<|old(l.Model())|::old(l.Model())[i]>=0
  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)
{
 var elem,elem2;
  var it1 := l.Begin(); 
  var it2:=l.Begin(); if (it2.HasNext()) {elem2:=it2.Next();}
  b:=true; 
  while (it1.HasNext() && b )
  decreases |l.Model()|-it1.Index()
  invariant l.Valid() && it1.Valid() && it1.Parent()==l && it1 in l.Iterators()
  invariant l.Model()==old(l.Model())
  invariant 0<=it1.Index()<=|old(l.Model())|
  invariant b==forall i | 0<=i<it1.Index():: old(l.Model())[i]>=0
  invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  invariant fresh(l.Repr()-old(l.Repr()))
  invariant forall x | x in l.Repr() :: allocated(x)
   { elem:=it1.Next(); 
     b:=elem>=0;
   }
}


method  allEqual(l: List) returns (b:bool)
  modifies l,l.Repr()
  requires l.Valid()
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures b== forall i| 0<=i<|old(l.Model())|-1::old(l.Model())[i]==old(l.Model())[i+1]
  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)
{
 var elem,elem2;
  var it1 := l.Begin(); 
  var it2:=l.Begin(); if (it1.HasNext()) {elem:=it1.Next();}
  b:=true; 
  while (it1.HasNext() && b )
  decreases |l.Model()|-it1.Index()
  invariant l.Valid() && it1.Valid() && it1.Parent()==l && it1 in l.Iterators()
  invariant it2.Valid() && it2.Parent()==l && it2 in l.Iterators()
  invariant l.Model()==old(l.Model())
  invariant 0<=it1.Index()<=|old(l.Model())| 
  invariant it2.HasNext() ==> it2.Index()==it1.Index()-1
  invariant it1.HasNext()==>it2.HasNext()
  invariant b==forall i | 0<=i<it1.Index()-1:: old(l.Model())[i]==old(l.Model())[i+1]
  invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  invariant fresh(l.Repr()-old(l.Repr()))
  invariant forall x | x in l.Repr() :: allocated(x)
   {  
     elem2:=it2.Next();
     elem:=it1.Next();
     b:=elem==elem2;
   }
   
}
method IteratorExample2(l: List)
  modifies l, l.Repr()
  requires l.Valid()
  requires l.Model() != []
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)
{

  var it1 := l.Begin();
  var it2 := l.Begin();
}

method  IteratorExample3(l: LinkedList)
  modifies l, l.Repr()
  requires l.Valid()
  requires l.Model() != []
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)
{
  var it1 := l.Begin();
  var it2 := l.Begin();
  var x := it2.Next();
  var y := l.PopFront();
  assert x == y;
  //assert !it1.Valid();  // we cannot prove nor disprove this assertion
  assert it2.Valid();
}
method  IteratorExample4(l: List)
modifies l, l.Repr()
  requires l.Valid()
    requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)

{
  var it1 := l.Begin();
  var it2 := l.Begin();
  it1:=l.Insert(it1,2);it1:=l.Insert(it1,2);
  var b:=it1.HasNext();
  if (it1.HasNext()) {it1:=l.Erase(it1);it1:=l.Insert(it1,4);}

}
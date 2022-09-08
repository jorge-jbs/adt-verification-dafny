include "../../src/Utils.dfy"
include "../../src/tree/layer1/OrderedSetL.dfy"




method ordSetContained(s1:OrderedSet,s2:OrderedSet) returns (b:bool)
modifies s1, s1.Repr(), s2, s2.Repr()
requires s1.Valid() && s2.Valid()
requires forall x | x in s1.Repr() :: allocated(x)
requires forall x | x in s2.Repr() :: allocated(x)

requires ({s1} + s1.Repr()) !! ({s2}+s2.Repr())
ensures s1.Valid() && s2.Valid()
ensures s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
ensures b == isSubSet(s1.Model(),s2.Model())

ensures forall x {:trigger x in s1.Repr(), x in old(s1.Repr())} | x in s1.Repr() - old(s1.Repr()) :: fresh(x)
ensures fresh(s1.Repr()-old(s1.Repr()))
ensures forall x | x in s1.Repr() :: allocated(x)

ensures forall x {:trigger x in s2.Repr(), x in old(s2.Repr())} | x in s2.Repr() - old(s2.Repr()) :: fresh(x)
ensures fresh(s2.Repr()-old(s2.Repr()))
ensures forall x | x in s2.Repr() :: allocated(x)

ensures s1.Iterators()>=old(s1.Iterators()) && s2.Iterators()>=old(s2.Iterators())
{
 var it1:=s1.First(); var x1:int; var x2:int;
 var it2:=s2.First(); b:=true;
 while (it1.HasNext() && it2.HasNext() && b)
   decreases |s1.Model()|+|s2.Model()|-(it1.Index()+it2.Index())+(if b then 1 else 0)
   invariant s1.Valid() && s2.Valid() 
   invariant ({s1} + s1.Repr()) !! ({s2}+s2.Repr()) 
   invariant s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
   invariant it1.Valid() && it2.Valid() 
   invariant it1 in s1.Iterators() && it2 in s2.Iterators()
   invariant it1.Parent()==s1 && it2.Parent()==s2
   invariant 0<=it1.Index()<=|s1.Model()| && 0<=it2.Index()<=|s2.Model()|
   //invariant !it2.HasNext()==> b
   invariant b ==> isSubSet(s1.Model()[..it1.Index()],s2.Model()[..it2.Index()])
   invariant !b ==> !isSubSet(s1.Model()[..it1.Index()],s2.Model())
   invariant it1.HasNext() ==> s1.Model()[it1.Index()] !in s2.Model()[..it2.Index()]
   invariant forall u::0<=u<it2.Index() && it1.Index()<|s1.Model()| ==> s2.Model()[u]<s1.Model()[it1.Index()]
   
   invariant forall x {:trigger x in s1.Repr(), x in old(s1.Repr())} | x in s1.Repr() - old(s1.Repr()) :: fresh(x)
   invariant forall x {:trigger x in s2.Repr(), x in old(s2.Repr())} | x in s2.Repr() - old(s2.Repr()) :: fresh(x)
   invariant forall x | x in s1.Repr() :: allocated(x)
   invariant forall x | x in s2.Repr() :: allocated(x)
   invariant s1.Iterators() >= old(s1.Iterators()) && s2.Iterators() >= old(s2.Iterators())

 { 
   assert it1.Index()<|s1.Model()| && it2.Index()<|s2.Model()|;
  if (it1.Peek()==it2.Peek())
  { 
     lmoreSubSet(s1.Model(),s2.Model(),it1.Index(),it2.Index());
     x1 := it1.Next(); x2:=it2.Next(); 
   
  }
  else if (it1.Peek()<it2.Peek())
   { 
     lnotSubSet(s1.Model(),s2.Model(),it1.Index(),it2.Index());
     b:=false;  
     x1:=it1.Next();
    }
  else { 
    lmoreSubSet2(s1.Model(),s2.Model(),it1.Index(),it2.Index());
    x2 := it2.Next();
    }
  
 }
 
 lSubSet(s1.Model(),s2.Model(),it2.Index());
 assert b && !it1.HasNext() ==> isSubSet(s1.Model(),s2.Model());
 assert b && it1.HasNext() ==> !it2.HasNext() && s1.Model()[it1.Index()] !in s2.Model()[..it2.Index()] ==> s1.Model()[it1.Index()] !in s2.Model();
  
  
  b:=b && !it1.HasNext();

}


include "../../src/Utils.dfy"
include "../../src/tree/layer1/OrderedSet.dfy"




method ordSetIntersection(s1:OrderedSet,s2:OrderedSet,su:OrderedSet)
modifies s1, s1.Repr(), s2, s2.Repr(), su, su.Repr()
requires s1.Valid() && s2.Valid() && su.Valid()
requires forall x | x in s1.Repr() :: allocated(x)
requires forall x | x in s2.Repr() :: allocated(x)
requires forall x | x in su.Repr() :: allocated(x)

requires ({s1} + s1.Repr()) !! ({s2}+s2.Repr())
requires ({s1} + s1.Repr()) !! ({su}+su.Repr())
requires ({su} + su.Repr()) !! ({s2}+s2.Repr())
requires su.Model()=={}

ensures s1.Valid() && s2.Valid() && su.Valid()
ensures s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
ensures su.Model() == (s1.Model() * s2.Model())

ensures forall x {:trigger x in s1.Repr(), x in old(s1.Repr())} | x in s1.Repr() - old(s1.Repr()) :: fresh(x)
ensures fresh(s1.Repr()-old(s1.Repr()))
ensures forall x | x in s1.Repr() :: allocated(x)

ensures forall x {:trigger x in s2.Repr(), x in old(s2.Repr())} | x in s2.Repr() - old(s2.Repr()) :: fresh(x)
ensures fresh(s2.Repr()-old(s2.Repr()))
ensures forall x | x in s2.Repr() :: allocated(x)

ensures forall x {:trigger x in su.Repr(), x in old(su.Repr())} | x in su.Repr() - old(su.Repr()) :: fresh(x)
ensures fresh(su.Repr()-old(su.Repr()))
ensures forall x | x in su.Repr() :: allocated(x)

ensures s1.Iterators()>=old(s1.Iterators()) && 
        s2.Iterators()>=old(s2.Iterators()) &&
        su.Iterators()>=old(su.Iterators())
{

 var it1:=s1.First(); var x1:int; var x2:int;
 var it2:=s2.First(); 

 while (it1.HasNext() && it2.HasNext())
   decreases (s1.Model()-it1.Traversed())+(s2.Model()-it2.Traversed())
   invariant s1.Valid() && s2.Valid() && su.Valid()
   invariant ({s1} + s1.Repr()) !! ({s2}+s2.Repr()) 
   invariant ({s1} + s1.Repr()) !! ({su}+su.Repr())
   invariant ({su} + su.Repr()) !! ({s2}+s2.Repr())
   invariant s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
   
   invariant it1.Valid() && it2.Valid() 
   invariant it1 in s1.Iterators() && it2 in s2.Iterators()
   invariant it1.Parent()==s1 && it2.Parent()==s2
   invariant it1.Traversed()<=s1.Model() && it2.Traversed()<=s2.Model()
   invariant su.Model()==it1.Traversed() * it2.Traversed()

   invariant forall x,y | x in it1.Traversed() && y in s2.Model()-it2.Traversed():: x<y
   invariant forall x,y | x in it2.Traversed() && y in s1.Model()-it1.Traversed():: x<y
   
   
   invariant forall x {:trigger x in s1.Repr(), x in old(s1.Repr())} | x in s1.Repr() - old(s1.Repr()) :: fresh(x)
   invariant forall x {:trigger x in s2.Repr(), x in old(s2.Repr())} | x in s2.Repr() - old(s2.Repr()) :: fresh(x)
   invariant forall x {:trigger x in su.Repr(), x in old(su.Repr())} | x in su.Repr() - old(su.Repr()) :: fresh(x)
   invariant forall x | x in s1.Repr() :: allocated(x)
   invariant forall x | x in s2.Repr() :: allocated(x)
   invariant forall x | x in su.Repr() :: allocated(x)
   invariant s1.Iterators() >= old(s1.Iterators()) &&
             s2.Iterators() >= old(s2.Iterators()) &&
             su.Iterators() >= old(su.Iterators())

 { ghost var oit1:=it1.Traversed(); ghost var oit2:=it2.Traversed();
  if (it1.Peek()==it2.Peek())
  { 
        su.add(it1.Peek()); 
        x1 := it1.Next();
        x2 := it2.Next();
  }
  else if (it1.Peek()<it2.Peek())
   { 
     x1:=it1.Next();
    }
  else { 
    x2 := it2.Next();
    }
  //assert it1.Traversed()>=oit1 && it2.Traversed()>=oit2;
  //assert it1.Traversed()>oit1 || it2.Traversed()>oit2;
  assert (s1.Model()-it1.Traversed())<s1.Model()-oit1 || (s2.Model()-it2.Traversed())<s2.Model()-oit2;
  assert (s1.Model()-it1.Traversed())+(s2.Model()-it2.Traversed())<(s1.Model()-oit1)+(s2.Model()-oit2);
  
 }

}


include "../../src/Utils.dfy"
include "../../src/tree/layer1/UnorderedSet.dfy"




method unordSetContained(s1:UnorderedSet,s2:UnorderedSet) returns (b:bool)
modifies s1, s1.Repr(), s2, s2.Repr()
requires s1.Valid() && s2.Valid()
requires forall x | x in s1.Repr() :: allocated(x)
requires forall x | x in s2.Repr() :: allocated(x)

requires ({s1} + s1.Repr()) !! ({s2}+s2.Repr())
ensures s1.Valid() && s2.Valid()
ensures s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
ensures b == (s1.Model() <= s2.Model())

ensures forall x {:trigger x in s1.Repr(), x in old(s1.Repr())} | x in s1.Repr() - old(s1.Repr()) :: fresh(x)
ensures fresh(s1.Repr()-old(s1.Repr()))
ensures forall x | x in s1.Repr() :: allocated(x)

ensures forall x {:trigger x in s2.Repr(), x in old(s2.Repr())} | x in s2.Repr() - old(s2.Repr()) :: fresh(x)
ensures fresh(s2.Repr()-old(s2.Repr()))
ensures forall x | x in s2.Repr() :: allocated(x)

ensures s1.Iterators()>=old(s1.Iterators()) && s2.Iterators()>=old(s2.Iterators())
{
 var it1:=s1.First(); var x1:int; var it2:UnorderedSetIterator;
 assert it1.Traversed()=={};
  b:=true;
 while (it1.HasNext() && b)
   decreases s1.Model()-it1.Traversed(),b
   invariant s1.Valid() && s2.Valid() 
   invariant ({s1} + s1.Repr()) !! ({s2}+s2.Repr()) 
   invariant s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
   invariant it1.Valid() 
   invariant it1 in s1.Iterators() 
   invariant it1.Parent()==s1 
   invariant it1.Traversed()<=s1.Model() 
   invariant b == (it1.Traversed() <= s2.Model())
   
   invariant forall x {:trigger x in s1.Repr(), x in old(s1.Repr())} | x in s1.Repr() - old(s1.Repr()) :: fresh(x)
   invariant forall x {:trigger x in s2.Repr(), x in old(s2.Repr())} | x in s2.Repr() - old(s2.Repr()) :: fresh(x)
   invariant forall x | x in s1.Repr() :: allocated(x)
   invariant forall x | x in s2.Repr() :: allocated(x)
   invariant s1.Iterators() >= old(s1.Iterators()) && s2.Iterators() >= old(s2.Iterators())

 { 
   it2 := s2.find(it1.Peek());
   b := it2.HasNext();
   x1:=it1.Next();

 }
}


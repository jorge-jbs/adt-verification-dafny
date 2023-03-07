include "../../src/tree/layer1/UnorderedSet.dfy"

method {:timelimitMultiplier 10} UnordSetIntersection(s1:UnorderedSet,s2:UnorderedSet,su:UnorderedSet)
modifies s1, s1.Repr(), s2, s2.Repr(), su, su.Repr()
requires allocated(s1.Repr())
requires allocated(s2.Repr())
requires allocated(su.Repr())
ensures allocated(s1.Repr())
ensures allocated(s2.Repr())
ensures allocated(su.Repr())

ensures fresh(s1.Repr()-old(s1.Repr()))
ensures fresh(s2.Repr()-old(s2.Repr()))
ensures fresh(su.Repr()-old(su.Repr()))

requires s1.Valid() && s2.Valid() && su.Valid()

requires ({s1} + s1.Repr()) !! ({s2}+s2.Repr())
requires ({s1} + s1.Repr()) !! ({su}+su.Repr())
requires ({su} + su.Repr()) !! ({s2}+s2.Repr())
requires su.Model()=={}

ensures s1.Valid() && s2.Valid() && su.Valid()
ensures s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
ensures su.Model() == (s1.Model() * s2.Model())

ensures s1.Iterators()>=old(s1.Iterators()) && 
        s2.Iterators()>=old(s2.Iterators()) &&
        su.Iterators()>=old(su.Iterators())
{

 var it1:=s1.First(); 
 var it1HasPeek := it1.HasPeek();
 while (it1HasPeek)
   decreases (s1.Model()-it1.Traversed())
   invariant allocated(s1.Repr())
   invariant allocated(s2.Repr())
   invariant allocated(su.Repr())

   invariant fresh(s1.Repr()-old(s1.Repr()))
   invariant fresh(s2.Repr()-old(s2.Repr()))
   invariant fresh(su.Repr()-old(su.Repr()))

   invariant s1.Valid() && s2.Valid() && su.Valid()
   invariant ({s1} + s1.Repr()) !! ({s2}+s2.Repr()) 
   invariant ({s1} + s1.Repr()) !! ({su}+su.Repr())
   invariant ({su} + su.Repr()) !! ({s2}+s2.Repr())
   invariant s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
   
   invariant it1.Valid() 
   invariant it1 in s1.Iterators() 
   invariant it1.Parent()==s1 
   invariant it1.Traversed() <= s1.Model() 
   invariant su.Model() == it1.Traversed() * s2.Model()
   invariant it1HasPeek == it1.HasPeek?()

   invariant s1.Iterators() >= old(s1.Iterators()) &&
             s2.Iterators() >= old(s2.Iterators()) &&
             su.Iterators() >= old(su.Iterators())
{  
   var it1Peek := it1.Peek();
   var it2 := s2.Find(it1Peek);
   var it2HasPeek := it2.HasPeek();
   if (it2HasPeek) 
     { su.Add(it1Peek); }
   it1.Next();
   it1HasPeek := it1.HasPeek();
 }
}


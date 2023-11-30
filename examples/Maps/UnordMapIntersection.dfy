include "../../src/UnorderedMap/UnorderedMapSpec.dfy"

module UnordMapIntersection{
  import opened UnorderedMapSpec
  import opened KeyValue

  export provides KeyValue, UnorderedMapSpec, UnordMapIntersection
         reveals combineVs

ghost function combineVs(v1:V,v2:V):V 
{ if (v1 <= v2) then v1 else v2}

method combineValues(v1:V,v2:V) returns (v:V)
ensures v == combineVs(v1,v2)

method {:timelimitMultiplier 10} UnordMapIntersection(s1:UnorderedMap,s2:UnorderedMap,su:UnorderedMap)
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
requires su.Model()== map[]

ensures s1.Valid() && s2.Valid() && su.Valid()
ensures s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
ensures su.Model() == map i | i in s1.Model() && i in s2.Model() :: combineVs(s1.Model()[i],s2.Model()[i]) 
                          

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
   invariant it1.Traversed() <= s1.Model().Keys 
   invariant su.Model() == map i | i in it1.Traversed() && i in s2.Model() :: combineVs(s1.Model()[i],s2.Model()[i]) 
   invariant it1HasPeek == it1.HasPeek?()

   invariant s1.Iterators() >= old(s1.Iterators()) &&
             s2.Iterators() >= old(s2.Iterators()) &&
             su.Iterators() >= old(su.Iterators())
{  
   var it1Peek := it1.Peek();
   var it2 := s2.Find(it1Peek.0);
   var it2HasPeek := it2.HasPeek();
   if (it2HasPeek) 
     {var it2Peek := it2.Peek();
      var newV := combineValues(it1Peek.1,it2Peek.1); 
      su.Add(it1Peek.0,newV); }
   it1.Next();
   it1HasPeek := it1.HasPeek();
 }
}

}
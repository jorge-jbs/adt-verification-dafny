include "../../src/UnorderedMultiset/UnorderedMultisetSpec.dfy"
include "../../src/Collections/KeyValue.dfy"

module UnordMultisetIntersection{
  import opened UnorderedMultisetSpec
  import opened KeyValue
  
  export provides KeyValue, UnorderedMultisetSpec, UnordMultisetAdd, UnordMultisetIntersection


method {:timelimitMultiplier 10} UnordMultisetAdd(s:UnorderedMultiset,x:K,m:nat)
modifies s, s.Repr()
requires allocated(s.Repr())
ensures allocated(s.Repr())
ensures fresh(s.Repr()-old(s.Repr()))
requires s.Valid() 
ensures s.Valid()
ensures s.Model()==old(s.Model())[x:= old(s.Model()[x]) + m]
ensures s.Iterators()>=old(s.Iterators())
{
 var i := 0;
 while (i < m)
 decreases m - i
 invariant 0 <=i <= m
 invariant allocated(s.Repr())
 invariant fresh(s.Repr()-old(s.Repr()))
 invariant s.Valid() 
 invariant s.Model()==old(s.Model())[x:= old(s.Model()[x]) + i]
 invariant s.Iterators()>=old(s.Iterators()) 
 {
   s.Add(x);
   i := i + 1;

 }
}

method {:timelimitMultiplier 10} UnordMultisetAddIntersection(s1:UnorderedMultiset,s2:UnorderedMultiset,su:UnorderedMultiset,x:K)
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
requires su.Model()[x] == 0


ensures s1.Valid() && s2.Valid() && su.Valid()
ensures ({s1} + s1.Repr()) !! ({s2}+s2.Repr())
ensures ({s1} + s1.Repr()) !! ({su}+su.Repr())
ensures ({su} + su.Repr()) !! ({s2}+s2.Repr())
ensures s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
ensures if (s1.Model()[x]<s2.Model()[x]) 
        then su.Model()[x] == s1.Model()[x]
       else su.Model()[x] == s2.Model()[x]
ensures forall y |  y !=x ::  su.Model()[y] == old(su.Model()[y])

ensures s1.Iterators()>=old(s1.Iterators()) && 
        s2.Iterators()>=old(s2.Iterators()) &&
        su.Iterators()>=old(su.Iterators())
ensures forall it | it in old(s1.Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Traversed() == old(it.Traversed()) 
      && |it.Traversed()| == old(|it.Traversed()|)  
      && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))
ensures forall it | it in old(s2.Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Traversed() == old(it.Traversed()) 
      && |it.Traversed()| == old(|it.Traversed()|)  
      && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

{
 var c1 := s1.Count(x);
 var c2 := s2.Count(x);
 if (c1 < c2)
  {UnordMultisetAdd(su,x,c1);}
 else
  {UnordMultisetAdd(su,x,c2);}
}


method {:timelimitMultiplier 10} UnordMultisetIntersection(s1:UnorderedMultiset,s2:UnorderedMultiset,su:UnorderedMultiset)
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
requires su.Model()==multiset{}

ensures s1.Valid() && s2.Valid() && su.Valid()
ensures ({s1} + s1.Repr()) !! ({s2}+s2.Repr())
ensures ({s1} + s1.Repr()) !! ({su}+su.Repr())
ensures ({su} + su.Repr()) !! ({s2}+s2.Repr())
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
   invariant {it1} !! ({s2}+s2.Repr())
   invariant {it1} !! ({su}+su.Repr())
   invariant it1.Parent()==s1 
   invariant it1.Traversed() <= s1.Model() 
   invariant forall x | x in it1.Traversed() :: 
       if (s1.Model()[x]<s2.Model()[x]) 
        then su.Model()[x] == s1.Model()[x]
      else su.Model()[x] == s2.Model()[x]
   invariant forall x | x in su.Model() :: x in it1.Traversed() && x in s2.Model() 

   invariant it1HasPeek == it1.HasPeek?()

   invariant s1.Iterators() >= old(s1.Iterators()) &&
             s2.Iterators() >= old(s2.Iterators()) &&
             su.Iterators() >= old(su.Iterators())
{  
   var it1Peek := it1.Peek();
   var countPu := su.Count(it1Peek);
   if (countPu == 0)
    {UnordMultisetAddIntersection(s1,s2,su,it1Peek);
    }
   it1.Next();
   it1HasPeek := it1.HasPeek();
 }
}

}


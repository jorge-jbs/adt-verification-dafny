include "../../src/UnorderedMultiset/UnorderedMultisetSpec.dfy"

module UnordMultisetContained{
  import opened UnorderedMultisetSpec
  
  export provides UnorderedMultisetSpec, UnordMultisetContained

method UnordMultisetContained(s1:UnorderedMultiset,s2:UnorderedMultiset) returns (b:bool)
modifies s1, s1.Repr(), s2, s2.Repr()
requires allocated(s1.Repr())
requires allocated(s2.Repr())
ensures allocated(s1.Repr())
ensures allocated(s2.Repr())
ensures fresh(s1.Repr()-old(s1.Repr()))
ensures fresh(s2.Repr()-old(s2.Repr()))

requires s1.Valid() && s2.Valid()
ensures s1.Valid() && s2.Valid()

requires ({s1} + s1.Repr()) !! ({s2}+s2.Repr())

ensures s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
ensures b == forall x | x in s1.Model() :: x in s2.Model() && s1.Model()[x] <= s2.Model()[x]

ensures s1.Iterators() >= old(s1.Iterators()) && s2.Iterators() >= old(s2.Iterators())
{
 var it1:=s1.First(); var it2:UnorderedMultisetIterator;
 assert it1.Traversed()==multiset{};

 b:=true;
 var it1HasPeek := it1.HasPeek();
 
 while (it1HasPeek && b)
   decreases s1.Model()-it1.Traversed(),b
   invariant  allocated(s1.Repr())
   invariant allocated(s2.Repr())
   invariant fresh(s1.Repr()-old(s1.Repr()))
   invariant fresh(s2.Repr()-old(s2.Repr()))

   invariant s1.Valid() && s2.Valid() 
   invariant ({s1} + s1.Repr()) !! ({s2}+s2.Repr()) 
   invariant s1.Model()==old(s1.Model()) && s2.Model()==old(s2.Model())
   invariant it1.Valid() 
   invariant it1 in s1.Iterators() 
   invariant it1.Parent()==s1 
   invariant it1.Traversed()<=s1.Model() 
   invariant b == forall x | x in it1.Traversed() :: x in s2.Model() && s1.Model()[x] <= s2.Model()[x]
   invariant it1HasPeek == it1.HasPeek?()
   
   invariant s1.Iterators() >= old(s1.Iterators()) && s2.Iterators() >= old(s2.Iterators())
 { 
   var p := it1.Peek();
   var countP1 := s1.Count(p);
   var countP2 := s2.Count(p);
   b := (countP1 <= countP2); //each element must be repeated less times
   it1.Next();
   it1HasPeek := it1.HasPeek();

 }
}

}

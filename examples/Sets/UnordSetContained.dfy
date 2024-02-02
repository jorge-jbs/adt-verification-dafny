include "../../src/UnorderedSet/UnorderedSetSpec.dfy"

module UnordSetContained{
  import opened UnorderedSetSpec
  
  export provides UnorderedSetSpec, UnordSetContained

method UnordSetContained(s1:UnorderedSet,s2:UnorderedSet) returns (b:bool)
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
ensures b == (s1.Model() <= s2.Model())

ensures s1.Iterators() >= old(s1.Iterators()) && s2.Iterators() >= old(s2.Iterators())
{
 var it1:=s1.First(); var it2:UnorderedSetIterator;
 assert it1.Traversed()=={};

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
   invariant b == (it1.Traversed() <= s2.Model())
   invariant it1HasPeek == it1.HasPeek?()
   
   invariant s1.Iterators() >= old(s1.Iterators()) && s2.Iterators() >= old(s2.Iterators())
 { 
   var p := it1.Peek();
   it2 := s2.Find(p);
   b := it2.HasPeek();
   it1.Next();
   it1HasPeek := it1.HasPeek();

 }
}

}
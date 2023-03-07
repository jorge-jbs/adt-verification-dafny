include "../../src/tree/layer1/OrderedSet.dfy"


method {:timeLimitMultiplier 20} OrdSetContained(s1:OrderedSet,s2:OrderedSet) returns (b:bool)
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

ensures s1.Iterators()>=old(s1.Iterators()) && s2.Iterators()>=old(s2.Iterators())
{
 var it1:OrderedSetIterator:=s1.First(); var x1:int; var x2:int;
 var it2:OrderedSetIterator:=s2.First(); 
 assert it1.Traversed()==it2.Traversed()=={};

 var it1HasPeek := it1.HasPeek();
 var it2HasPeek := it2.HasPeek();
 b:=true;

 while (it1HasPeek && it2HasPeek && b)
  // decreases s1.Model()+s2.Model()-(it1.Traversed()+it2.Traversed()),b
  //decreases s2.Model()-it2.Traversed(),b
  decreases |s2.Model()|-it2.Index(),b
   invariant  allocated(s1.Repr())
   invariant allocated(s2.Repr())
   invariant fresh(s1.Repr()-old(s1.Repr()))
   invariant fresh(s2.Repr()-old(s2.Repr()))

   invariant s1.Valid() && s2.Valid() 
   invariant ({s1} + s1.Repr()) !! ({s2}+s2.Repr()) 
   invariant s1.Model() == old(s1.Model()) && s2.Model() == old(s2.Model())
   invariant it1.Valid() && it2.Valid() 
   invariant it1 in s1.Iterators() && it2 in s2.Iterators()
   invariant it1.Parent() == s1 && it2.Parent() == s2
   invariant it1.Traversed() <= s1.Model() && it2.Traversed() <= s2.Model()
   invariant 0 <= it1.Index() <= |s1.Model()| && 0 <= it2.Index() <= |s2.Model()|
   //invariant !it2.HasNext()==> b
   invariant b ==> it1.Traversed() <= it2.Traversed()
   invariant !b ==> !(it1.Traversed() <= s2.Model())
   invariant it1.HasPeek?() ==> it1.Peek?() !in it2.Traversed()
   invariant forall u | u in it2.Traversed() && it1.Traversed() < s1.Model() :: u < it1.Peek?()

   invariant it1HasPeek == it1.HasPeek?()
   invariant it2HasPeek == it2.HasPeek?()

   invariant s1.Iterators() >= old(s1.Iterators()) && s2.Iterators() >= old(s2.Iterators())
 { 

  var it1Peek := it1.Peek();
  var it2Peek := it2.Peek();
  if (it1Peek == it2Peek)
  { 
        it1.Next(); it2.Next(); 
   
  }
  else if (it1Peek <it2Peek)
   { 
      assert s2.Model() == it2.Traversed()+{it2.Peek?()}+(s2.Model()-it2.Traversed()-{it2.Peek?()});
      assert it1.Peek?() !in it2.Traversed();
      assert forall z | z in s2.Model()-it2.Traversed()-{it2.Peek?()} :: it1.Peek?() < it2.Peek?() < z;
     b:=false;  
     it1.Next();
    }
  else { 
    it2.Next();
    }
  it1HasPeek := it1.HasPeek();
  it2HasPeek := it2.HasPeek();
 }
  
  b := b && !it1HasPeek;

}


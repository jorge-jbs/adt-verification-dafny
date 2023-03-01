include "../../src/tree/layer1/OrderedSet.dfy"




method {:timeLimitMultiplier 20} OrdSetIntersection(s1:OrderedSet,s2:OrderedSet,su:OrderedSet)
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
//ensures su.Model() == (s1.Model() * s2.Model())

ensures s1.Iterators()>=old(s1.Iterators()) && 
        s2.Iterators()>=old(s2.Iterators()) &&
        su.Iterators()>=old(su.Iterators())
{

 var it1:OrderedSetIterator:=s1.First(); 
 var it2:OrderedSetIterator:=s2.First(); 
 var it1HasPeek := it1.HasPeek();
 var it2HasPeek := it2.HasPeek();


 while (it1HasPeek && it2HasPeek)
   //decreases (s1.Model()-it1.Traversed()) +(s2.Model()-it2.Traversed())
   decreases |s1.Model()|-it1.Index(), |s2.Model()|-it2.Index()
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
   invariant s1.Model() == old(s1.Model()) && s2.Model() == old(s2.Model())
   invariant |s1.Model()| == old(|s1.Model()|) && |s2.Model()| == old(|s2.Model()|)
   
   invariant it1 is OrderedSetIterator
   invariant it1.Valid() 
   invariant it1 in s1.Iterators() 
   invariant it1.Parent() == s1 
   invariant 0 <= it1.Index() <= |s1.Model()|
   invariant it1HasPeek == it1.HasPeek?()
   
   invariant it2 is OrderedSetIterator
   invariant it2.Valid() 
   invariant it2 in s2.Iterators() 
   invariant it2.Parent() == s2 
   invariant 0 <= it2.Index() <= |s2.Model()|
   invariant it2HasPeek == it2.HasPeek?()

   //invariant forall x,y | x in it1.Traversed() && y in (s2.Model()-it2.Traversed()) :: x < y
   //invariant forall x,y | x in it2.Traversed() && y in (s1.Model()-it1.Traversed()) :: x < y
   //invariant su.Model() == it1.Traversed() * it2.Traversed()

   invariant s1.Iterators() >= old(s1.Iterators()) &&
             s2.Iterators() >= old(s2.Iterators()) &&
             su.Iterators() >= old(su.Iterators())


 { 
  ghost var oit1 := it1.Index();
  ghost var oit2 := it2.Index();


  
  assert oit1 >= 0 && oit2 >= 0; 
  var it1Peek := it1.Peek();
  var it2Peek := it2.Peek();
  if (it1Peek == it2Peek)
    { 
        su.Add(it1Peek); 
        it1.Next();
        it2.Next();
        assert it1.Index() > oit1;
        assert it2.Index() > oit2;
        //assume |s1.Model()| == os1 && |s2.Model()| == os2;
        //assert |s1.Model()|-it1.Index() < os1-oit1;
        //assert |s2.Model()|-it1.Index() < os2-oit2;

    }
  else if (it1Peek < it2Peek)
    { 
     //assert forall y | y in s2.Model()-it2.Traversed():: it1.Peek?()<it2.Peek?()<=y;
       it1.Next();
       assert it1.Index() > oit1;
       assert it2.Index() == oit2;
       //        assume |s1.Model()| == os1 && |s2.Model()| == os2;
       //assert |s1.Model()|-it1.Index() < os1-oit1;
       //assert |s2.Model()|-it2.Index() == os2-oit2;

    }
  else 
    { 
    //assert forall y | y in s1.Model()-it1.Traversed():: it2.Peek?()<it1.Peek?()<=y;
      it2.Next();
      assert it1.Index() == oit1;
      assert it2.Index() > oit2;
      //        assume |s1.Model()| == os1 && |s2.Model()| == os2;
      //assert |s1.Model()|-it1.Index() == os1-oit1;
      // assert |s2.Model()|-it2.Index() < os2-oit2;
    }
  it1HasPeek := it1.HasPeek();
  it2HasPeek := it2.HasPeek();


  
}

/*assert  su.Model() == it1.Traversed() * it2.Traversed();
calc =={
s1.Model() * s2.Model();
((s1.Model()-it1.Traversed())+it1.Traversed()) * s2.Model();
(s1.Model()-it1.Traversed())* s2.Model() + it1.Traversed() * s2.Model();
(s1.Model()-it1.Traversed())* s2.Model() + su.Model();
{assume (s1.Model()-it1.Traversed())* s2.Model()=={};}
su.Model();


 }*/

}


include "../../src/List/ListSpec.dfy"
include "../../src/LinkedList/LinkedListSpec.dfy"
include "../../src/Order.dfy"

module Merge{
  import opened ListSpec
  import opened LinkedListSpec
  import opened Order

ghost predicate Smaller(xs1:seq<int>,xs2:seq<int>)
{forall i,j:: 0 <= i < |xs1| && 0 <= j < |xs2| ==> xs1[i] <= xs2[j]}

method Merge(l1:LinkedList<int>,l2:LinkedList<int>,ml:LinkedList<int>)
  modifies l1, l1.Repr(), l2, l2.Repr(),ml, ml.Repr()
  requires allocated(l1.Repr())
  requires allocated(l2.Repr())
  requires allocated(ml.Repr())
  ensures fresh(l1.Repr()-old(l1.Repr()))
  ensures allocated(l1.Repr())
  ensures fresh(l2.Repr()-old(l2.Repr()))
  ensures allocated(l2.Repr())
  ensures fresh(ml.Repr()-old(ml.Repr()))
  ensures allocated(ml.Repr())

  requires l1.Valid() && l2.Valid() && ml.Valid() && ml.Empty?()
  requires {l1}+l1.Repr()!!{l2}+l2.Repr()  && {l1}+l1.Repr()!!{ml}+ml.Repr() && {l2}+l2.Repr()!!{ml}+ml.Repr()
  requires  Sorted(l1.Model()) && Sorted(l2.Model())

  ensures l1.Valid() && l2.Valid() && ml.Valid()
  ensures l1.Model() == old(l1.Model()) && l2.Model() == old(l2.Model())
  ensures Sorted(ml.Model())
  ensures multiset(ml.Model()) == multiset(l1.Model())+multiset(l2.Model())
  ensures {l1}+l1.Repr()!!{l2}+l2.Repr()  && {l1}+l1.Repr()!!{ml}+ml.Repr() && {l2}+l2.Repr()!!{ml}+ml.Repr()

  ensures l1.Iterators() >= old(l1.Iterators()) && l2.Iterators() >= old(l2.Iterators())
  ensures forall it | it in old(l1.Iterators()) && old(it.Valid()) ::
    && it.Valid() 
    && it.Parent() == old(it.Parent()) 
    && old(it.Index()) == it.Index()
  ensures forall it | it in old(l2.Iterators()) && old(it.Valid()) ::
    && it.Valid() 
    && it.Parent() == old(it.Parent()) 
    && old(it.Index()) == it.Index()
{

  var it1,it2 := copyMerge(l1,l2,ml);
  var it1HasPeek := it1.HasPeek();
  var it2HasPeek := it2.HasPeek();

  assert multiset(ml.Model()) == multiset(l1.Model()[..it1.Index()])+multiset(l2.Model()[..it2.Index()]);
  

  if it1HasPeek
    { 
    var oldit1Index := it1.Index();

     copyRest(l1,ml,it1); 
     
     assert multiset(ml.Model()) == multiset(l1.Model())+multiset(l2.Model()[..it2.Index()]) by
     {
      assert it1.Index() == |l1.Model()| && l1.Model()[..it1.Index()] == l1.Model();
      calc{
        multiset(ml.Model());
        multiset(l1.Model()[..oldit1Index])+multiset(l2.Model()[..it2.Index()])+multiset(l1.Model()[oldit1Index..]);
         {assert l1.Model() == l1.Model()[..oldit1Index] + l1.Model()[oldit1Index..]; }
        multiset(l1.Model()) + multiset(l2.Model()[..it2.Index()]);
      }
     }
    }
  else { assert it1.Index() == |l1.Model()| && l1.Model()[..it1.Index()] == l1.Model(); }  
  if it2HasPeek 
    { 
      var oldit2Index := it2.Index();
      assert multiset(ml.Model()) == multiset(l1.Model()) + multiset(l2.Model()[..oldit2Index]);

      copyRest(l2,ml,it2); 
      
      assert multiset(ml.Model()) == multiset(l1.Model())+multiset(l2.Model()) by
      {
       assert it2.Index() == |l2.Model()| && l2.Model()[..it2.Index()] == l2.Model();
       calc{
         multiset(ml.Model());
         multiset(l1.Model())+multiset(l2.Model()[..oldit2Index])+multiset(l2.Model()[oldit2Index..]);
          {assert l2.Model() == l2.Model()[..oldit2Index] + l2.Model()[oldit2Index..]; }
         multiset(l1.Model()) + multiset(l2.Model());
        }
      }
    }
    else {assert it2.Index() == |l2.Model()| && l2.Model()[..it2.Index()] == l2.Model();}
}


method copyRest(l:LinkedList<int>,ml:LinkedList<int>, itl:ListIterator<int>)
  modifies l, l.Repr(), ml, ml.Repr()
  requires allocated(l.Repr())
  requires allocated(ml.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())
  ensures fresh(ml.Repr()-old(ml.Repr()))
  ensures allocated(ml.Repr())

  requires l.Valid() && ml.Valid() 
  requires {l}+l.Repr()!!{ml}+ml.Repr()  
  requires itl.Valid() && itl in l.Iterators() 
  requires itl.Parent() == l && 0 <= itl.Index() < |l.Model()|
  requires  Sorted(l.Model()) && Sorted(ml.Model()) 
  requires Smaller(ml.Model(),l.Model()[itl.Index()..])

  ensures  l.Valid() && ml.Valid()
  ensures  l.Model() == old(l.Model()) 
  ensures  itl.Valid() && itl in l.Iterators() 
  ensures  itl.Parent() == l && itl.Index() == |l.Model()|
  ensures Sorted(ml.Model())
  ensures ml.Model() == old(ml.Model()) + l.Model()[old(itl.Index())..]
  ensures multiset(ml.Model()) == multiset(old(ml.Model())) + multiset(l.Model()[old(itl.Index())..])

  ensures {l}+l.Repr()!!{ml}+ml.Repr()

  ensures l.Iterators() >= old(l.Iterators()) && ml.Iterators() >= old(ml.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && it != itl ::
    && it.Valid() 
    && it.Parent() == old(it.Parent()) 
    && old(it.Index()) == it.Index()
{ var itlHasPeek := itl.HasPeek();

  while (itlHasPeek)
    decreases |l.Model()| - itl.Index()
    invariant fresh(l.Repr()-old(l.Repr()))
    invariant allocated(l.Repr())
    invariant fresh(ml.Repr()-old(ml.Repr()))
    invariant allocated(ml.Repr())

    invariant l.Valid() && ml.Valid()
    invariant itl in l.Iterators() 
    invariant itl.Parent() == l 
    invariant itl.Valid() 
    invariant itl.Index() >= 0  
    invariant l.Model() == old(l.Model()) 
    invariant Sorted(ml.Model()) && Sorted(l.Model()) 
    invariant Smaller(ml.Model(),l.Model()[itl.Index()..])
    invariant ml.Model() == old(ml.Model())+l.Model()[old(itl.Index())..itl.Index()]
    invariant itlHasPeek == itl.HasPeek?()

    invariant l.Iterators() >= old(l.Iterators()) && ml.Iterators() >= old(ml.Iterators())
    invariant forall it | it in old(l.Iterators()) && old(it.Valid()) && it != itl ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && old(it.Index()) == it.Index()
    invariant  {l}+l.Repr()!!{ml}+ml.Repr() 
   {

    ghost var modell := l.Model()[old(itl.Index())..itl.Index()];
    assert l.Model()[old(itl.Index())..itl.Index()+1] == l.Model()[old(itl.Index())..itl.Index()]+[l.Model()[itl.Index()]];
    var x:= itl.Peek();
    itl.Next();

    assert l.Model()[old(itl.Index())..itl.Index()] == modell + [x];
    ghost var model := ml.Model();

    ml.PushBack(x);

    assert multiset(ml.Model()) == multiset(model)+multiset{x};

    itlHasPeek := itl.HasPeek();

   }
   assert multiset(ml.Model()) == old(multiset(ml.Model())) + multiset(l.Model()[old(itl.Index())..itl.Index()]);
   assert l.Model()[old(itl.Index())..itl.Index()] == l.Model()[old(itl.Index())..];

}

method copyMerge(l1:LinkedList<int>,l2:LinkedList<int>, ml:LinkedList<int>) returns (it1:ListIterator<int>, it2:ListIterator<int>)
   modifies l1, l1.Repr(), l2, l2.Repr(),ml, ml.Repr()
  requires allocated(l1.Repr())
  requires allocated(l2.Repr())
  requires allocated(ml.Repr())
  ensures fresh(l1.Repr()-old(l1.Repr()))
  ensures allocated(l1.Repr())
  ensures fresh(l2.Repr()-old(l2.Repr()))
  ensures allocated(l2.Repr())
  ensures fresh(ml.Repr()-old(ml.Repr()))
  ensures allocated(ml.Repr())

  requires l1.Valid() && l2.Valid() 
  requires ml.Valid() && ml.Empty?()
  requires {l1}+l1.Repr()!!{l2}+l2.Repr()  && {l1}+l1.Repr()!!{ml}+ml.Repr() && {l2}+l2.Repr()!!{ml}+ml.Repr()
  requires  Sorted(l1.Model()) && Sorted(l2.Model())

  ensures l1.Valid() && l2.Valid() && ml.Valid()
  ensures l1.Model() == old(l1.Model()) && l2.Model() == old(l2.Model())
  ensures {l1}+l1.Repr()!!{l2}+l2.Repr()  && {l1}+l1.Repr()!!{ml}+ml.Repr() && {l2}+l2.Repr()!!{ml}+ml.Repr()

  ensures fresh(it1) && fresh(it2)
  ensures it1.Valid() && it1.Parent() == l1  
  ensures it2.Valid() && it2.Parent() == l2 
  ensures it1.Index() >=0 && it2.Index() >=0
  ensures it1.Index()+it2.Index() == |ml.Model()|
  ensures it1.Index() == |l1.Model()| || it2.Index() == |l2.Model()|  
  
  ensures Sorted(ml.Model())
  ensures  Smaller(ml.Model(),l1.Model()[it1.Index()..]) && Smaller(ml.Model(),l2.Model()[it2.Index()..])
  ensures multiset(ml.Model()) == multiset(l1.Model()[..it1.Index()])+multiset(l2.Model()[..it2.Index()])

  ensures l1.Iterators() >= old(l1.Iterators()) + {it1} && l2.Iterators() >= old(l2.Iterators())+{it2}
  ensures forall it | it in old(l1.Iterators()) && old(it.Valid()) ::
    && it.Valid() 
    && it.Parent() == old(it.Parent()) 
    && old(it.Index()) == it.Index()
  ensures forall it | it in old(l2.Iterators()) && old(it.Valid()) ::
    && it.Valid() 
    && it.Parent() == old(it.Parent()) 
    && old(it.Index()) == it.Index()

{  it1 := l1.First();
   it2 := l2.First();
  var it1HasPeek := it1.HasPeek();
  var it2HasPeek := it2.HasPeek();

  while (it1HasPeek && it2HasPeek)
    decreases |l1.Model()| + |l2.Model()|- (it1.Index()+it2.Index())
    invariant fresh(l1.Repr()-old(l1.Repr()))
    invariant allocated(l1.Repr())
    invariant fresh(l2.Repr()-old(l2.Repr()))
    invariant allocated(l2.Repr())
    invariant fresh(ml.Repr()-old(ml.Repr()))
    invariant allocated(ml.Repr())

    invariant l1.Valid() && l2.Valid() && ml.Valid()
    invariant it1 in l1.Iterators() && it2 in l2.Iterators()
    invariant it1.Parent() == l1 && it2.Parent() == l2
    invariant it1.Valid() && it2.Valid()
    invariant 0 <= it1.Index() <= |l1.Model()| && 0 <= it2.Index() <= |l2.Model()|
    invariant l1.Model() == old(l1.Model()) && l2.Model() == old(l2.Model())
    invariant it1.Index()+it2.Index() == |ml.Model()|
    invariant Sorted(ml.Model()) && Sorted(l1.Model()) && Sorted(l2.Model())
    invariant Smaller(ml.Model(),l1.Model()[it1.Index()..]) && Smaller(ml.Model(),l2.Model()[it2.Index()..])
    invariant multiset(ml.Model()) == multiset(l1.Model()[..it1.Index()])+multiset(l2.Model()[..it2.Index()])
    invariant it1HasPeek == it1.HasPeek?()
    invariant it2HasPeek == it2.HasPeek?()
    
    invariant l1.Iterators() >= old(l1.Iterators()) + {it1} && l2.Iterators() >= old(l2.Iterators())+{it2}
    invariant forall it | it in old(l1.Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && old(it.Index()) == it.Index()
    invariant forall it | it in old(l2.Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && old(it.Index()) == it.Index()

    invariant {l1}+l1.Repr()!!{l2}+l2.Repr()  && {l1}+l1.Repr()!!{ml}+ml.Repr() && {l2}+l2.Repr()!!{ml}+ml.Repr()
  {
    ghost var model1 := l1.Model()[..it1.Index()]; 
    ghost var model2 := l2.Model()[..it2.Index()];

    var it1Peek := it1.Peek();
    var it2Peek := it2.Peek();
    var x;
    if (it1Peek <= it2Peek) {
      x := it1Peek;
      it1.Next();        
      assert l1.Model()[..it1.Index()] == model1+[x];
      assert multiset(l1.Model()[..it1.Index()]) == multiset(model1+[x]);
    }
    else {
      x := it2Peek;
      it2.Next();        
      assert l2.Model()[..it2.Index()] == model2+[x];
      assert multiset(l2.Model()[..it2.Index()]) == multiset{x}+multiset(model2);
    }
      
    ghost var model := ml.Model();

    ml.PushBack(x);
    assert multiset(ml.Model()) == multiset(model)+multiset{x};
    
    it1HasPeek := it1.HasPeek();
    it2HasPeek := it2.HasPeek();
    }
  assert it1.Index() == |l1.Model()| || it2.Index() == |l2.Model()|;
}


}




include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"
include "../../src/UtilsAux.dfy"

predicate smaller(xs1:seq<int>,xs2:seq<int>)
{forall i,j:: 0<=i<|xs1| && 0<=j<|xs2| ==> xs1[i]<=xs2[j]}

method {:timeLimitMultiplier 100} {:verify true} merge(l1:LinkedList<int>,l2:LinkedList<int>,ml:LinkedList<int>)
//method {:timeLimitMultiplier 6} {:verify true} merge(l1:ArrayList,l2:ArrayList,ml:ArrayList) //NO CHANGES
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
  ensures l1.Model()==old(l1.Model()) && l2.Model()==old(l2.Model())
  ensures Sorted(ml.Model())
  ensures multiset(ml.Model())==multiset(l1.Model())+multiset(l2.Model())
  ensures {l1}+l1.Repr()!!{l2}+l2.Repr()  && {l1}+l1.Repr()!!{ml}+ml.Repr() && {l2}+l2.Repr()!!{ml}+ml.Repr()

  ensures l1.Iterators() >= old(l1.Iterators()) && l2.Iterators() >= old(l2.Iterators())
  ensures forall it | it in old(l1.Iterators()) && old(it.Valid())::
      it.Valid() && it.Parent()==old(it.Parent()) && old(it.Index())== it.Index()
  ensures forall it | it in old(l2.Iterators()) && old(it.Valid())::
      it.Valid() && it.Parent()==old(it.Parent()) && old(it.Index())== it.Index()
{
  var it1:=l1.Begin();
  var it2:=l2.Begin();
  var it1HasNext := it1.HasNext();
  var it2HasNext := it2.HasNext();

  while (it1HasNext && it2HasNext)
    decreases |l1.Model()| + |l2.Model()|- (it1.Index()+it2.Index())
    invariant fresh(l1.Repr()-old(l1.Repr()))
    invariant allocated(l1.Repr())
    invariant fresh(l2.Repr()-old(l2.Repr()))
    invariant allocated(l2.Repr())
    invariant fresh(ml.Repr()-old(ml.Repr()))
    invariant allocated(ml.Repr())

    invariant l1.Valid() && l2.Valid() && ml.Valid()
    invariant it1 in l1.Iterators() && it2 in l2.Iterators()
    invariant it1.Parent() == l1 && it2.Parent()==l2
    invariant it1.Valid() && it2.Valid()
    invariant l1.Model()==old(l1.Model()) && l2.Model()==old(l2.Model())
    invariant it1.Index()+it2.Index() == |ml.Model()|
    invariant Sorted(ml.Model()) && Sorted(l1.Model()) && Sorted(l2.Model())
    invariant smaller(ml.Model(),l1.Model()[it1.Index()..]) && smaller(ml.Model(),l2.Model()[it2.Index()..])
    invariant multiset(ml.Model())==multiset(l1.Model()[..it1.Index()])+multiset(l2.Model()[..it2.Index()])
    invariant it1HasNext == it1.HasNext?()
    invariant it2HasNext == it2.HasNext?()
    
    invariant l1.Iterators() >= old(l1.Iterators()) && l2.Iterators() >= old(l2.Iterators())
    invariant forall it | it in old(l1.Iterators()) && old(it.Valid())::
      it.Valid() && it.Parent()==old(it.Parent()) && old(it.Index())== it.Index()
    invariant forall it | it in old(l2.Iterators()) && old(it.Valid())::
      it.Valid() && it.Parent()==old(it.Parent()) && old(it.Index())== it.Index()

    invariant {l1}+l1.Repr()!!{l2}+l2.Repr()  && {l1}+l1.Repr()!!{ml}+ml.Repr() && {l2}+l2.Repr()!!{ml}+ml.Repr()
  {
    ghost var model1:=l1.Model()[..it1.Index()]; 
    ghost var model2:=l2.Model()[..it2.Index()];

    var it1Peek := it1.Peek();
    var it2Peek := it2.Peek();
    var x;
    if (it1Peek <= it2Peek) {

      x := it1.Next();        
      assert l1.Model()[..it1.Index()]==model1+[x];
      assert multiset(l1.Model()[..it1.Index()])==multiset(model1+[x]);
    }
    else {
      
      x:=it2.Next();        
      assert l2.Model()[..it2.Index()]==model2+[x];
      assert multiset(l2.Model()[..it2.Index()])==multiset{x}+multiset(model2);
    }
      
    ghost var model:=ml.Model();

    ml.PushBack(x);
    assert multiset(ml.Model())==multiset(model)+multiset{x};
    
    it1HasNext := it1.HasNext();
    it2HasNext := it2.HasNext();
    }
  assert it1.Index()==|l1.Model()| || it2.Index()==|l2.Model()|;

  it1HasNext := it1.HasNext();
  while (it1HasNext)
    decreases |l1.Model()| + |l2.Model()|- (it1.Index()+it2.Index())
    invariant fresh(l1.Repr()-old(l1.Repr()))
    invariant allocated(l1.Repr())
    invariant fresh(l2.Repr()-old(l2.Repr()))
    invariant allocated(l2.Repr())
    invariant fresh(ml.Repr()-old(ml.Repr()))
    invariant allocated(ml.Repr())

    invariant l1.Valid() && l2.Valid() && ml.Valid()
    invariant it1 in l1.Iterators() && it2 in l2.Iterators()
    invariant it1.Parent() == l1 && it2.Parent()==l2
    invariant it1.Valid() && it2.Valid()
    invariant l1.Model()==old(l1.Model()) && l2.Model()==old(l2.Model())
    invariant it1.Index()+it2.Index() == |ml.Model()|
    invariant Sorted(ml.Model()) && Sorted(l1.Model()) && Sorted(l2.Model())
    invariant smaller(ml.Model(),l1.Model()[it1.Index()..]) && smaller(ml.Model(),l2.Model()[it2.Index()..])
    invariant it1.HasNext?() ==> it2.Index()==|l2.Model()|
    invariant multiset(ml.Model())==multiset(l1.Model()[..it1.Index()])+multiset(l2.Model()[..it2.Index()])
    invariant it1HasNext == it1.HasNext?()
  
    invariant l1.Iterators() >= old(l1.Iterators()) && l2.Iterators() >= old(l2.Iterators())
    invariant forall it | it in old(l1.Iterators()) && old(it.Valid())::
      it.Valid() && it.Parent()==old(it.Parent()) && old(it.Index())== it.Index()
    invariant forall it | it in old(l2.Iterators()) && old(it.Valid())::
      it.Valid() && it.Parent()==old(it.Parent()) && old(it.Index())== it.Index()

    invariant {l1}+l1.Repr()!!{l2}+l2.Repr()  && {l1}+l1.Repr()!!{ml}+ml.Repr() && {l2}+l2.Repr()!!{ml}+ml.Repr()
   {
      ghost var model1:=l1.Model()[..it1.Index()];

    var x:=it1.Next();

    assert l1.Model()[..it1.Index()]==model1+[x];
    assert multiset(l1.Model()[..it1.Index()])==multiset(model1+[x]);
    ghost var model:=ml.Model();

    ml.PushBack(x);

    assert multiset(ml.Model())==multiset(model)+multiset{x};

    it1HasNext := it1.HasNext();
    }

  it2HasNext := it2.HasNext();

  while (it2HasNext)
    decreases |l1.Model()| + |l2.Model()|- (it1.Index()+it2.Index())
    invariant fresh(l1.Repr()-old(l1.Repr()))
    invariant allocated(l1.Repr())
    invariant fresh(l2.Repr()-old(l2.Repr()))
    invariant allocated(l2.Repr())
    invariant fresh(ml.Repr()-old(ml.Repr()))
    invariant allocated(ml.Repr())

    invariant l1.Valid() && l2.Valid() && ml.Valid()
    invariant it1 in l1.Iterators() && it2 in l2.Iterators()
    invariant it1.Parent() == l1 && it2.Parent()==l2
    invariant it1.Valid() && it2.Valid()
    invariant l1.Model()==old(l1.Model()) && l2.Model()==old(l2.Model())
    invariant it1.Index()+it2.Index() == |ml.Model()|
    invariant it1.Index()==|l1.Model()|
    invariant Sorted(ml.Model()) && Sorted(l1.Model()) && Sorted(l2.Model())
    invariant smaller(ml.Model(),l2.Model()[it2.Index()..])
    invariant it2.HasNext?() ==> it1.Index()==|l1.Model()|
    invariant multiset(ml.Model())==multiset(l1.Model()[..it1.Index()])+multiset(l2.Model()[..it2.Index()])
    invariant it2HasNext == it2.HasNext?()

    invariant l1.Iterators() >= old(l1.Iterators()) && l2.Iterators() >= old(l2.Iterators())
    invariant forall it | it in old(l1.Iterators()) && old(it.Valid())::
      it.Valid() && it.Parent()==old(it.Parent()) && old(it.Index())== it.Index()
    invariant forall it | it in old(l2.Iterators()) && old(it.Valid())::
      it.Valid() && it.Parent()==old(it.Parent()) && old(it.Index())== it.Index()

    invariant {l1}+l1.Repr()!!{l2}+l2.Repr()  && {l1}+l1.Repr()!!{ml}+ml.Repr() && {l2}+l2.Repr()!!{ml}+ml.Repr()
   {
    ghost var model2:=l2.Model()[..it2.Index()];

    var x:=it2.Next();

    assert l2.Model()[..it2.Index()]==model2+[x];
    assert multiset(l2.Model()[..it2.Index()])==multiset(model2+[x]);
    ghost var model:=ml.Model();

    ml.PushBack(x);

      assert multiset(ml.Model())==multiset(model)+multiset{x};

    it2HasNext := it2.HasNext();

   }

  assert it1.Index()==|l1.Model()| && it2.Index()==|l2.Model()|;
  assert l1.Model()[..it1.Index()]==l1.Model();
  assert l2.Model()[..it2.Index()]==l2.Model();

}

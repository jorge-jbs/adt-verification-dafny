include "../../src/linear/adt/List.dfy"
include "../../src/linear/impl/LinkedList.dfy"
include "../../src/linear/impl/VectorImpl.dfy"
include "../../src/UtilsAux.dfy"

predicate smaller(xs1:seq<int>,xs2:seq<int>)
{forall i,j:: 0<=i<|xs1| && 0<=j<|xs2| ==> xs1[i]<=xs2[j]}

method {:timeLimitMultiplier 6} {:verify true} merge(l1:LinkedList,l2:LinkedList,ml:LinkedList)
//method {:timeLimitMultiplier 6} {:verify true} merge(l1:ArrayList,l2:ArrayList,ml:ArrayList) //NO CHANGES
  modifies l1, l1.Repr(), l2, l2.Repr(),ml, ml.Repr()
  requires l1.Valid() && l2.Valid() && ml.Valid() && ml.Empty()
  requires forall x | x in l1.Repr() :: allocated(x)
  requires forall x | x in l2.Repr() :: allocated(x)
  requires forall x | x in ml.Repr() :: allocated(x)
  requires {l1}+l1.Repr()!!{l2}+l2.Repr()  && {l1}+l1.Repr()!!{ml}+ml.Repr() && {l2}+l2.Repr()!!{ml}+ml.Repr()
  requires  Sorted(l1.Model()) && Sorted(l2.Model())

  ensures l1.Valid() && l2.Valid() && ml.Valid()
  ensures l1.Model()==old(l1.Model()) && l2.Model()==old(l2.Model())
  ensures Sorted(ml.Model())
  ensures multiset(ml.Model())==multiset(l1.Model())+multiset(l2.Model())

  ensures l1.Iterators() >= old(l1.Iterators()) && l2.Iterators() >= old(l2.Iterators())
  ensures forall it | it in old(l1.Iterators()) && old(it.Valid())::
      it.Valid() && old(it.Index())== it.Index()
  ensures forall it | it in old(l2.Iterators()) && old(it.Valid())::
      it.Valid() && old(it.Index())== it.Index()

  ensures forall x {:trigger x in l1.Repr(), x in old(l1.Repr())} | x in l1.Repr() && x !in old(l1.Repr()) :: fresh(x)
  ensures fresh(l1.Repr()-old(l1.Repr()))
  ensures forall x | x in l1.Repr() :: allocated(x)
  ensures forall x {:trigger x in l2.Repr(), x in old(l2.Repr())} | x in l2.Repr() && x !in old(l2.Repr()) :: fresh(x)
  ensures fresh(l2.Repr()-old(l2.Repr()))
  ensures forall x | x in l2.Repr() :: allocated(x)
  ensures forall x {:trigger x in ml.Repr(), x in old(ml.Repr())} | x in ml.Repr() && x !in old(ml.Repr()) :: fresh(x)
  ensures fresh(ml.Repr()-old(ml.Repr()))
  ensures forall x | x in ml.Repr() :: allocated(x)
{
  var it1:=l1.Begin();
  var it2:=l2.Begin();
  var x;
  while (it1.HasNext() && it2.HasNext())
    decreases |l1.Model()| + |l2.Model()|- (it1.Index()+it2.Index())
    invariant l1.Valid() && l2.Valid() && ml.Valid()
    invariant it1 in l1.Iterators() && it2 in l2.Iterators()
    invariant it1.Parent() == l1 && it2.Parent()==l2
    invariant it1.Valid() && it2.Valid()
    invariant l1.Model()==old(l1.Model()) && l2.Model()==old(l2.Model())
    invariant it1.Index()+it2.Index() == |ml.Model()|
    invariant Sorted(ml.Model()) && Sorted(l1.Model()) && Sorted(l2.Model())
    invariant smaller(ml.Model(),l1.Model()[it1.Index()..]) && smaller(ml.Model(),l2.Model()[it2.Index()..])
    invariant multiset(ml.Model())==multiset(l1.Model()[..it1.Index()])+multiset(l2.Model()[..it2.Index()])

    invariant l1.Iterators() >= old(l1.Iterators()) && l2.Iterators() >= old(l2.Iterators())
    invariant forall it | it in old(l1.Iterators()) && old(it.Valid())::
      it.Valid() && old(it.Index())== it.Index()
    invariant forall it | it in old(l2.Iterators()) && old(it.Valid())::
      it.Valid() && old(it.Index())== it.Index()

    invariant {l1}+l1.Repr()!!{l2}+l2.Repr()  && {l1}+l1.Repr()!!{ml}+ml.Repr() && {l2}+l2.Repr()!!{ml}+ml.Repr()
    invariant forall x {:trigger x in l1.Repr(), x in old(l1.Repr())} | x in l1.Repr() && x !in old(l1.Repr()) :: fresh(x)
    invariant forall x {:trigger x in l2.Repr(), x in old(l2.Repr())} | x in l2.Repr() && x !in old(l2.Repr()) :: fresh(x)
    invariant forall x {:trigger x in ml.Repr(), x in old(ml.Repr())} | x in ml.Repr() && x !in old(ml.Repr()) :: fresh(x)
    invariant forall x | x in l1.Repr() :: allocated(x)
    invariant forall x | x in l2.Repr() :: allocated(x)
    invariant forall x | x in ml.Repr() :: allocated(x)
  {
      ghost var model1:=l1.Model()[..it1.Index()]; 
      ghost var model2:=l2.Model()[..it2.Index()];

    if it1.Peek() <= it2.Peek() {

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

    }


    assert it1.Index()==|l1.Model()| || it2.Index()==|l2.Model()|;

   while (it1.HasNext())
   decreases |l1.Model()| + |l2.Model()|- (it1.Index()+it2.Index())
    invariant l1.Valid() && l2.Valid() && ml.Valid()
    invariant it1 in l1.Iterators() && it2 in l2.Iterators()
    invariant it1.Parent() == l1 && it2.Parent()==l2
    invariant it1.Valid() && it2.Valid()
    invariant l1.Model()==old(l1.Model()) && l2.Model()==old(l2.Model())
    invariant it1.Index()+it2.Index() == |ml.Model()|
    invariant Sorted(ml.Model()) && Sorted(l1.Model()) && Sorted(l2.Model())
    invariant smaller(ml.Model(),l1.Model()[it1.Index()..]) && smaller(ml.Model(),l2.Model()[it2.Index()..])
    invariant it1.HasNext() ==> it2.Index()==|l2.Model()|
    invariant multiset(ml.Model())==multiset(l1.Model()[..it1.Index()])+multiset(l2.Model()[..it2.Index()])

    invariant l1.Iterators() >= old(l1.Iterators()) && l2.Iterators() >= old(l2.Iterators())
    invariant forall it | it in old(l1.Iterators()) && old(it.Valid())::
      it.Valid() && old(it.Index())== it.Index()
    invariant forall it | it in old(l2.Iterators()) && old(it.Valid())::
      it.Valid() && old(it.Index())== it.Index()

    invariant {l1}+l1.Repr()!!{l2}+l2.Repr()  && {l1}+l1.Repr()!!{ml}+ml.Repr() && {l2}+l2.Repr()!!{ml}+ml.Repr()
    invariant forall x {:trigger x in l1.Repr(), x in old(l1.Repr())} | x in l1.Repr() && x !in old(l1.Repr()) :: fresh(x)
    invariant forall x {:trigger x in l2.Repr(), x in old(l2.Repr())} | x in l2.Repr() && x !in old(l2.Repr()) :: fresh(x)
    invariant forall x {:trigger x in ml.Repr(), x in old(ml.Repr())} | x in ml.Repr() && x !in old(ml.Repr()) :: fresh(x)
    invariant forall x | x in l1.Repr() :: allocated(x)
    invariant forall x | x in l2.Repr() :: allocated(x)
    invariant forall x | x in ml.Repr() :: allocated(x)
   {
      ghost var model1:=l1.Model()[..it1.Index()];

    x:=it1.Next();

       assert l1.Model()[..it1.Index()]==model1+[x];
       assert multiset(l1.Model()[..it1.Index()])==multiset(model1+[x]);
       ghost var model:=ml.Model();

    ml.PushBack(x);

       assert multiset(ml.Model())==multiset(model)+multiset{x};

    }

   while (it2.HasNext())
   decreases |l1.Model()| + |l2.Model()|- (it1.Index()+it2.Index())
    invariant l1.Valid() && l2.Valid() && ml.Valid()
    invariant it1 in l1.Iterators() && it2 in l2.Iterators()
    invariant it1.Parent() == l1 && it2.Parent()==l2
    invariant it1.Valid() && it2.Valid()
    invariant l1.Model()==old(l1.Model()) && l2.Model()==old(l2.Model())
    invariant it1.Index()+it2.Index() == |ml.Model()|
    invariant it1.Index()==|l1.Model()|
    invariant Sorted(ml.Model()) && Sorted(l1.Model()) && Sorted(l2.Model())
    invariant smaller(ml.Model(),l2.Model()[it2.Index()..])
    invariant it2.HasNext() ==> it1.Index()==|l1.Model()|
    invariant multiset(ml.Model())==multiset(l1.Model()[..it1.Index()])+multiset(l2.Model()[..it2.Index()])

    invariant l1.Iterators() >= old(l1.Iterators()) && l2.Iterators() >= old(l2.Iterators())
    invariant forall it | it in old(l1.Iterators()) && old(it.Valid())::
      it.Valid() && old(it.Index())== it.Index()
    invariant forall it | it in old(l2.Iterators()) && old(it.Valid())::
      it.Valid() && old(it.Index())== it.Index()

    invariant {l1}+l1.Repr()!!{l2}+l2.Repr()  && {l1}+l1.Repr()!!{ml}+ml.Repr() && {l2}+l2.Repr()!!{ml}+ml.Repr()
    invariant forall x {:trigger x in l1.Repr(), x in old(l1.Repr())} | x in l1.Repr() && x !in old(l1.Repr()) :: fresh(x)
    invariant forall x {:trigger x in l2.Repr(), x in old(l2.Repr())} | x in l2.Repr() && x !in old(l2.Repr()) :: fresh(x)
    invariant forall x {:trigger x in ml.Repr(), x in old(ml.Repr())} | x in ml.Repr() && x !in old(ml.Repr()) :: fresh(x)
    invariant forall x | x in l1.Repr() :: allocated(x)
    invariant forall x | x in l2.Repr() :: allocated(x)
    invariant forall x | x in ml.Repr() :: allocated(x)
   {
      ghost var model2:=l2.Model()[..it2.Index()];

    x:=it2.Next();

      assert l2.Model()[..it2.Index()]==model2+[x];
      assert multiset(l2.Model()[..it2.Index()])==multiset(model2+[x]);
      ghost var model:=ml.Model();

    ml.PushBack(x);

      assert multiset(ml.Model())==multiset(model)+multiset{x};


   }

  assert it1.Index()==|l1.Model()| && it2.Index()==|l2.Model()|;
  assert l1.Model()[..it1.Index()]==l1.Model();
  assert l2.Model()[..it2.Index()]==l2.Model();

}

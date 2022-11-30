include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"
include "Dup_Utils.dfy"
include "../../src/Iterators_Utils.dfy"


method DupElements<A>(l: LinkedList<A>) returns (ghost mit:map<int,int>)
  modifies l, l.Repr()
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires l.Valid()
  ensures l.Valid()
  ensures l.Model() == Dup(old(l.Model()))
  ensures |l.Model()| == 2 * |old(l.Model())|
  ensures forall i | 0<=i<|old(l.Model())| :: old(l.Model())[i] == l.Model()[2*i]==l.Model()[2*i+1]
  
  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::
     it.Valid() && it.Parent()==old(it.Parent()) && mit[old(it.Index())]==it.Index()
  ensures mit== dupMap(old(l.Model()),|old(l.Model())|)
  //ensures mit == buildMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),fdup(|old(l.Model())|))
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()):: old(it.Index()) in mit //domain
  ensures forall i | i in mit :: mit[i]==dup(i,|old(l.Model())|)//range
{

    //ghost var validSet:=(set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index()));
    //mit:=buildMap(validSet,identity);
     mit:= dupMap(old(l.Model()),0);

  var it := l.Begin();
  var b := it.HasNext();  
   
  ghost var i := 0;
  
  while b
    decreases |l.Model()| - it.Index()
    invariant allocated(l.Repr())
    invariant fresh(l.Repr()-old(l.Repr()))

    invariant l.Valid()
    invariant 2*i <= |l.Model()|
    invariant i <= old(|l.Model()|)
    invariant l.Model()[..2*i] == old(DupRev(l.Model()[..i]))
    invariant l.Model()[2*i..] == old(l.Model()[i..])
    invariant it.Parent() == l
    invariant it.Valid()
    invariant {it} !! {l}
    invariant it.Index() == 2*i
    invariant it in l.Iterators()
    invariant b == it.HasNext?()

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall iter | iter in old(l.Iterators()) && old(iter.Valid()) && old(iter.Index()) in mit::
       iter.Valid() && iter.Parent()==old(iter.Parent()) && mit[old(iter.Index())]==iter.Index()
    //invariant  mit == buildMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),fdupInvariant(i))
    invariant mit== dupMap(old(l.Model()),i)
  {

    assert i < old(|l.Model()|);
    ghost var omodel := l.Model();
    assert omodel[..2*i] == old(DupRev(l.Model()[..i]));
    assert omodel[2*i]==old(l.Model()[i]);

    var x := it.Peek();
    
    assert x==l.Model()[2*i]==old(l.Model()[i]);

    
    var it1:=l.Insert(it, x);

      ghost var model := l.Model();
      calc == {
       model;
       Seq.Insert(x, omodel, it.Index());
       omodel[..it.Index()] + [x] + omodel[it.Index()..];
       omodel[..2*i+1] + [x] + omodel[2*i+1..];
       omodel[..2*i] + [x] + [x] + omodel[2*i+1..];
       DupRev(old(l.Model()[..i])) + [x] + [x] + omodel[2*i+1..];
       DupRev(old(l.Model()[..i])) + [old(l.Model()[i])] + [old(l.Model()[i])] + omodel[2*i+1..];
       { assert old(l.Model()[..i+1][..|l.Model()[..i+1]|-1]) == old(l.Model()[..i]); }
       DupRev(old(l.Model()[..i+1])) + omodel[2*i+1..];
     }
     assert model == DupRev(old(l.Model()[..i+1])) + omodel[2*i+1..];

    var _ := it.Next();
    b := it.HasNext();
    i := i + 1;
    
     // mit:=buildMap(validSet,fdupInvariant(i));
     mit:=dupMap(old(l.Model()),i);
    }
 
 //mit:=buildMap(validSet,fdup(|old(l.Model())|));
  
  assert i==|old(l.Model())|;
  DupDupRev(old(l.Model()[..i]));
  assert old(l.Model()[..i]) == old(l.Model());
  //assert l.Model() == old(Dup(l.Model()));
  setDup(old(l.Model())); // 0->0,1 1-> 2,3 ...

}







method DupElementsAL(l: ArrayList<int>) returns (ghost mit:map<int,int>)
  modifies l, l.Repr()
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires l.Valid()
  ensures l.Valid()
  ensures l.Model() == old(Dup(l.Model()))
  ensures |l.Model()| == 2* |old(l.Model())|
  ensures forall i | 0<=i<|old(l.Model())| :: old(l.Model())[i] == l.Model()[2*i]==l.Model()[2*i+1]

  ensures l.Iterators() >= old(l.Iterators())
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()) && old(it.Index()) in mit::
      it.Valid() && it.Parent()==old(it.Parent()) && mit[old(it.Index())]==it.Index()
  ensures mit == buildMap((set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index())),identity)
  ensures forall it | it in old(l.Iterators()) && old(it.Valid()):: old(it.Index()) in mit //domain
  ensures forall i | i in mit :: mit[i]==identity(i)//range
{
     
    ghost var validSet:=(set it |it in old(l.Iterators()) && old(it.Valid())::old(it.Index()));
    mit:=buildMap(validSet,identity);


  var it := l.Begin();
  var b := it.HasNext();

  ghost var i := 0;
  
  while b
    decreases |l.Model()| - it.Index()
    invariant allocated(l.Repr())
    invariant fresh(l.Repr()-old(l.Repr()))

    invariant l.Valid()
    invariant 2*i <= |l.Model()|
    invariant i <= old(|l.Model()|)
    invariant l.Model()[..2*i] == old(DupRev(l.Model()[..i]))
    invariant l.Model()[2*i..] == old(l.Model()[i..])
    invariant it.Parent() == l
    invariant it.Valid()
    invariant {it} !! {l}
    invariant it.Index() == 2*i
    invariant it in l.Iterators()
    invariant b == it.HasNext?()

    invariant l.Iterators() >= old(l.Iterators())
    invariant it !in old(l.Iterators())
    invariant forall iter | iter in old(l.Iterators()) && old(iter.Valid()) && old(iter.Index()) in mit::
        iter.Valid() && iter.Parent()==old(iter.Parent()) && mit[old(iter.Index())]==iter.Index();
  {
     
     
    assert i < old(|l.Model()|);
    ghost var omodel := l.Model();
    assert omodel[..2*i] == old(DupRev(l.Model()[..i]));
    
    var x := it.Peek();    
    
    assert x==l.Model()[2*i];
    
    var it1:=l.Insert(it, x);
    
    ghost var model := l.Model();
    calc == {
       model;
       Seq.Insert(x, omodel, it.Index());
       omodel[..it.Index()] + [x] + omodel[it.Index()..];
       omodel[..2*i+1] + [x] + omodel[2*i+1..];
       omodel[..2*i] + [x] + [x] + omodel[2*i+1..];
       DupRev(old(l.Model()[..i])) + [x] + [x] + omodel[2*i+1..];
       DupRev(old(l.Model()[..i])) + [old(l.Model()[i])] + [old(l.Model()[i])] + omodel[2*i+1..];
       { assert old(l.Model()[..i+1][..|l.Model()[..i+1]|-1]) == old(l.Model()[..i]); }
       DupRev(old(l.Model()[..i+1])) + omodel[2*i+1..];
     }
    assert model == DupRev(old(l.Model()[..i+1])) + omodel[2*i+1..];


    var _ := it.Next();
    var _ := it.Next(); //In ArrayList index mid remains, so we jump over two elements to reach the following one
    b := it.HasNext();
    i := i + 1;


  }

  assert i==|old(l.Model())|;
  DupDupRev(old(l.Model()[..i]));
  assert old(l.Model()[..i]) == old(l.Model());

  //assert l.Model() == old(Dup(l.Model()));
  setDup(old(l.Model())); // 0->0,1 1-> 2,3 ...

}

method dupDup<A>(l:LinkedList<A>)returns (ghost mit:map<int,int>)
modifies l, l.Repr()
  requires l.Valid()
  requires forall x | x in l.Repr() :: allocated(x)

  ensures l.Valid()
  ensures l.Model() == Dup(Dup(old(l.Model())))
  {
    ghost var validSet:=(set it |it in old(l.Iterators()) && old(it.Valid())&& old(it.Index())<|old(l.Model())|);

    var mit1:=DupElements(l);
    var mit2:=DupElements(l);

    mit:= map it | it in mit1 ::mit2[mit1[it]];
    assert forall it | it in validSet :: it.Valid() && mit[old(it.Index())] == 4*old(it.Index())+3;
  }

  method DupElementsList<A>(l: List<A>) 
  modifies l, l.Repr()
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires l.Valid()
  ensures l.Valid()
  ensures l.Model() == Dup(old(l.Model()))
  ensures |l.Model()| == 2* |old(l.Model())|
  ensures forall i | 0<=i<|old(l.Model())| :: old(l.Model())[i] == l.Model()[2*i]==l.Model()[2*i+1]

  ensures l.Iterators() >= old(l.Iterators())
{
  var it := l.Begin();
  var b := it.HasNext();

  ghost var i := 0;
  
  while b
    decreases |l.Model()| - it.Index()
    invariant allocated(l.Repr())
    invariant fresh(l.Repr()-old(l.Repr()))

    invariant l.Valid()
    invariant 2*i <= |l.Model()|
    invariant i <= old(|l.Model()|)
    invariant l.Model()[..2*i] == DupRev(old(l.Model()[..i]))
    invariant l.Model()[2*i..] == old(l.Model()[i..])
    invariant it.Parent() == l
    invariant it.Valid()
    invariant {it} !! {l}
    invariant it.Index() == 2*i
    invariant it in l.Iterators()
    invariant b == it.HasNext?()

    invariant l.Iterators() >= old(l.Iterators())
    invariant it !in old(l.Iterators())
  {   
    assert i < old(|l.Model()|);
    ghost var omodel := l.Model();
    assert omodel[..2*i] == DupRev(old(l.Model()[..i]));
    assert it.Index()==2*i;
    
    var x := it.Peek();    
    
    assert x==l.Model()[2*i];

     it:=l.Insert(it, x);
    

    ghost var model := l.Model();
    calc == {
       model;
       Seq.Insert(x, omodel, it.Index());
       omodel[..it.Index()] + [x] + omodel[it.Index()..];
       omodel[..2*i+1] + [x] + omodel[2*i+1..];
       omodel[..2*i] + [x] + [x] + omodel[2*i+1..];
       DupRev(old(l.Model()[..i])) + [x] + [x] + omodel[2*i+1..];
       DupRev(old(l.Model()[..i])) + [old(l.Model()[i])] + [old(l.Model()[i])] + omodel[2*i+1..];
       { assert old(l.Model()[..i+1][..|l.Model()[..i+1]|-1]) == old(l.Model()[..i]); }
       DupRev(old(l.Model()[..i+1])) + omodel[2*i+1..];
     }
    assert model == DupRev(old(l.Model()[..i+1])) + omodel[2*i+1..];


    var _ := it.Next();
    var _ := it.Next(); 
    b := it.HasNext();
    i := i + 1;


  }

  assert i==|old(l.Model())|;
  DupDupRev(old(l.Model()[..i]));
  assert old(l.Model()[..i]) == old(l.Model());

  //assert l.Model() == old(Dup(l.Model()));
  setDup(old(l.Model())); // 0->0,1 1-> 2,3 ...

}

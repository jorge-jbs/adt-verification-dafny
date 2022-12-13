include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"
include "Dup_Utils.dfy"

method DupElements<A>(l: LinkedList<A>)
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
  ensures forall it | it in old(l.Iterators()) && old(it.Valid())::
      it.Valid() && it.Parent()==old(it.Parent()) &&
      if (old(it.Index())== |old(l.Model())|) then
           it.Index()==2*old(it.Index())
      else it.Index()==2*old(it.Index())+1 //Because we insert before
{

  var it := l.First();
  var b := it.HasPeek();

  ghost var i := 0;

  while b
    decreases |l.Model()| - it.Index()
    invariant allocated(l.Repr())
    invariant fresh(l.Repr()-old(l.Repr()))

    invariant l.Valid()
    invariant it in l.Iterators()
    invariant it.Parent() == l
    invariant it.Valid()
    invariant {it} !! {l}
    invariant it.Index() == 2*i <= |l.Model()|
    invariant i <= old(|l.Model()|)
    invariant l.Model()[..2*i] == DupRev(old(l.Model()[..i]))
    invariant l.Model()[2*i..] == old(l.Model()[i..])
    invariant b == it.HasPeek?()

    invariant l.Iterators() >= old(l.Iterators())
    invariant forall iter | iter in old(l.Iterators()) && old(iter.Valid())::
       iter.Valid() && iter.Parent()==old(iter.Parent()) &&
       (if (old(iter.Index())<i) then
            iter.Index()==2*old(iter.Index())+1
       else
           iter.Index()==i + old(iter.Index()))
  {
    ghost var omodel := l.Model();
    assert omodel[..2*i] == DupRev(old(l.Model()[..i]));
    assert omodel[2*i]==old(l.Model()[i]);

    var x := it.Peek();
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

    it.Next();
    b := it.HasPeek();
    i := i + 1;
  }

  assert i==|old(l.Model())|;
  DupDupRev(old(l.Model()[..i]));
  assert old(l.Model()[..i]) == old(l.Model());
  //assert l.Model() == old(Dup(l.Model()));
  setDup(old(l.Model())); // 0->0,1 1-> 2,3 ...
}

method DupElementsAL<A>(l: ArrayList<A>)
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
  ensures forall it | it in old(l.Iterators()) && old(it.Valid())::
      it.Valid() && it.Parent()==old(it.Parent()) && it.Index()==old(it.Index())
{
  var it := l.First();
  var b := it.HasPeek();

  ghost var i := 0;

  while b
    decreases |l.Model()| - it.Index()
    invariant allocated(l.Repr())
    invariant fresh(l.Repr()-old(l.Repr()))

    invariant l.Valid()
    invariant it in l.Iterators()
    invariant it.Parent() == l
    invariant it.Valid()
    invariant {it} !! {l}
    invariant it.Index() == 2*i <= |l.Model()|
    invariant i <= old(|l.Model()|)
    invariant l.Model()[..2*i] == DupRev(old(l.Model()[..i]))
    invariant l.Model()[2*i..] == old(l.Model()[i..])
    invariant b == it.HasPeek?()

    invariant l.Iterators() >= old(l.Iterators())
    invariant  forall it | it in old(l.Iterators()) && old(it.Valid())::
      it.Valid() && it.Parent()==old(it.Parent()) && it.Index()==old(it.Index())
  {
    assert i < old(|l.Model()|);
    ghost var omodel := l.Model();
    assert omodel[..2*i] == DupRev(old(l.Model()[..i]));

    var x := it.Peek();
    
    assert x==l.Model()[2*i];
    
    var it1:=l.Insert(it, x); //also it:=l.Insert(it,x);

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

    it.Next();
    it.Next(); //In ArrayList index mid remains, so we jump over two elements to reach the following one
    b := it.HasPeek();
    i := i + 1;
  }

  assert i==|old(l.Model())|;
  DupDupRev(old(l.Model()[..i]));
  assert old(l.Model()[..i]) == old(l.Model());

  assert l.Model() == Dup(old(l.Model()));
  setDup(old(l.Model())); // 0->0,1 1-> 2,3 ...
}

method dupDup<A>(l:LinkedList<A>) 
  modifies l, l.Repr()
  requires allocated(l.Repr())
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures allocated(l.Repr())

  requires l.Valid()
  ensures l.Valid()
  ensures l.Model() == Dup(Dup(old(l.Model())))
{
  ghost var validSet:=(set it |it in old(l.Iterators()) && old(it.Valid())&& old(it.Index())<|old(l.Model())|);

  DupElements(l);
  DupElements(l);

  assert forall it | it in validSet :: it.Valid() && it.Index() == 4*old(it.Index())+3;
}

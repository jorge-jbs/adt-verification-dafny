include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"

function Dup<A>(xs: seq<A>): seq<A>
{
  if xs == [] then
    []
  else
    [xs[0]] + [xs[0]] + Dup(xs[1..])
}

// This is the map that proves the subsequence property
function DupMap<A>(xs: seq<A>):map<int,int>
{
 map i | 0<=i<|xs| :: 2*i
}

function DupRev<A>(xs: seq<A>): seq<A>
  ensures 2*|xs| == |DupRev(xs)|
{
  if xs == [] then
    []
  else
    DupRev(xs[..|xs|-1]) + [xs[|xs|-1]] + [xs[|xs|-1]]
}

lemma DupDupRev<A>(xs: seq<A>)
  ensures Dup(xs) == DupRev(xs)
 {
   if |xs| <=1 {
   } else
    {
     calc == {
       Dup(xs);
       [xs[0]] + [xs[0]] + Dup(xs[1..]);
       [xs[0]] + [xs[0]] + DupRev(xs[1..]);
       {assert |xs[1..]|==|xs|-1 >=1;
       assert xs[1..][|xs|-2]== xs[|xs|-1];
       assert xs[1..][..|xs|-2]== xs[1..|xs|-1];}
       [xs[0]] + [xs[0]]  + (DupRev(xs[1..|xs|-1]) + [xs[|xs|-1]] + [xs[|xs|-1]]);
       DupRev(xs[..|xs|-1]) + [xs[|xs|-1]] + [xs[|xs|-1]];
       DupRev(xs);
     }
   }
 }

lemma {:induction xs} setDup<A>(xs: seq<A>)
ensures forall x :: x in xs <==> x in Dup(xs)
ensures |Dup(xs)|==2*|xs|
ensures forall i | 0<=i<|xs| :: xs[i]==Dup(xs)[2*i]==Dup(xs)[2*i+1]
{}

 lemma {:induction xs} dupElsAux<A>(xs: seq<A>,x:A)
 requires x in xs
 ensures multiset(Dup(xs))[x]==2*multiset(xs)[x]
{
    if (xs==[]){}
    else{
      if (x==xs[0]){
          if (xs[0] in xs[1..]){
            calc=={
              multiset(Dup(xs))[xs[0]];
              2+multiset(Dup(xs[1..]))[xs[0]];
              2+2*multiset(xs[1..])[xs[0]];
              2*(1+multiset(xs[1..])[xs[0]]);{assert xs==[xs[0]]+xs[1..];}
              2*multiset(xs)[xs[0]];
            }
        }
        else {
            assert xs[0] !in xs[1..];
            calc=={
              multiset(Dup(xs))[xs[0]];
              2+multiset(Dup(xs[1..]))[xs[0]];
              {setDup(xs[1..]);
              assert xs[0] !in xs[1..] ==> xs[0] !in Dup(xs[1..]);
              assert multiset(Dup(xs[1..]))[xs[0]]==0;}
              2;{assert xs==[xs[0]]+xs[1..];
                assert multiset(xs)[xs[0]]==1;}
              2*multiset(xs)[xs[0]];
            }
      }
      }
      else {
        calc=={
         multiset(Dup(xs))[x];
         multiset(Dup(xs[1..]))[x];{assert x in xs[1..];}
         2*multiset(xs[1..])[x];{assert xs==[xs[0]]+xs[1..];}
         2*multiset(xs)[x];
       }
      }
    }
}

lemma {:induction xs} dupEls<A>(xs: seq<A>)
 ensures forall x | x in xs :: multiset(Dup(xs))[x]==2*multiset(xs)[x]
{ forall x | x in xs
  ensures multiset(Dup(xs))[x]==2*multiset(xs)[x]{
   dupElsAux(xs,x);
  }
}


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

  var it := l.Begin();
  var b := it.HasNext();

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
    invariant b == it.HasNext?()

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
  var it := l.Begin();
  var b := it.HasNext();

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
    invariant b == it.HasNext?()

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

    var _ := it.Next();
    var _ := it.Next(); //In ArrayList index mid remains, so we jump over two elements to reach the following one
    b := it.HasNext();
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

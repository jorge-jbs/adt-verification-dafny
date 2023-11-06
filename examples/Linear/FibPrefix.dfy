
// Must be verified with -allocated:2

include "../../src/List/ListSpec.dfy"
include "../../src/LinkedList/LinkedListImpl.dfy"


module FibPrefix{
   import opened ListSpec
   import opened LinkedListImpl

ghost function Fib(n: nat): seq<nat>
  ensures |Fib(n)| == n
{
  if n <= 2 then
    [0, 1][..n]
  else
    var fib := Fib(n-1);
    fib + [fib[n-3] + fib[n-2]]
}

/*predicate ValidDistinct(adts: seq<ADT>)
  reads set r | r in adts :: r
  reads BigUnion(set r | r in adts :: r.Repr())
{
  && (forall r | r in adts :: r.Valid())
  && (forall r, s | r in adts && s in adts && [r, s] <= adts ::
        {r} + r.Repr() !! {s} + s.Repr())
}*/

method {:verify false} NextPrefix(pre: List<nat>, n: nat)
  modifies pre, pre.Repr()
  requires allocated(pre.Repr())
  ensures allocated(pre.Repr())
  ensures fresh(pre.Repr()-old(pre.Repr()))

  requires pre.Valid()
  ensures pre.Valid()

  requires n >= 2
  requires pre.Model() == Fib(n)
  ensures pre.Model() == Fib(n+1)
{
  var y := pre.PopBack();
  var x := pre.PopBack();
  pre.PushBack(x);
  pre.PushBack(y);
  pre.PushBack(x+y);
}

method {:verify false} Copy<A>(l: List<A>) returns (nl: List<A>)  // 49.9s
  modifies l, l.Repr()
  requires l.Valid()
  requires allocated(l.Repr())

  ensures allocated(l.Repr())
  ensures allocated(nl.Repr())
  ensures fresh(l.Repr() - old(l.Repr()))
  ensures fresh(nl)
  ensures fresh(nl.Repr())
  ensures ({l}+l.Repr()) !! ({nl}+nl.Repr())

  ensures l.Valid() && nl.Valid() 
  ensures l.Model() == old(l.Model())
  ensures nl.Model() == l.Model()
{
  nl := new LinkedListImpl();
  var it := l.First();
  var b := it.HasPeek();
  while b
    decreases |l.Model()| - it.Index()
    invariant allocated(l.Repr())
    invariant allocated(nl.Repr())
    invariant fresh(l.Repr() - old(l.Repr()))
    invariant fresh(nl)
    invariant fresh(nl.Repr())
    invariant ({l}+l.Repr()) !! ({nl}+nl.Repr())

    invariant l.Valid() && nl.Valid() 
    invariant it.Valid()
    invariant it.Parent() == l
    invariant b == it.HasPeek?()

    invariant l.Model() == old(l.Model())
    invariant 0 <= it.Index() <= |old(l.Model())|
    invariant nl.Model() == l.Model()[..it.Index()]
  {
    var x := it.Peek();
    it.Next();
    nl.PushBack(x);
    b := it.HasPeek();
  }
}

method {:verify false} FibPrefixes2() returns (pres: List<List<nat>>)  // 45s
  ensures allocated(pres.Repr())
  ensures fresh(pres)
  ensures fresh(pres.Repr())
  ensures pres.Valid()
  ensures forall pre | pre in pres.Model() ::
    && allocated(pre.Repr())
    && fresh(pre)
    && fresh(pre.Repr())
  ensures forall r | r in pres.Model() :: r.Valid()
  ensures forall i, j | 0 <= i < j < |pres.Model()| ::
    && pres.Model()[i] != pres.Model()[j]
    && pres.Model()[i] !in pres.Model()[j].Repr()
    && pres.Model()[j] !in pres.Model()[i].Repr()
    && pres.Model()[i].Repr() !! pres.Model()[j].Repr()
  ensures forall pre | pre in pres.Model() :: {pres} + pres.Repr() !! {pre} + pre.Repr()
  ensures forall i | 0 <= i < |pres.Model()| ::
    pres.Model()[i].Model() == Fib(i+1)
  ensures |pres.Model()| == 2
{
  pres := new LinkedListImpl();
  
  var pre0: List<nat> := new LinkedListImpl();
  pre0.PushBack(0);
  pres.PushBack(pre0);
  
  var pre1: List<nat> := new LinkedListImpl();
  pre1.PushBack(0);
  pre1.PushBack(1);
  pres.PushBack(pre1);
  
  assert |pres.Model()| == 2;
  assert pre0.Valid();
  assert pre1.Valid();
  assert pre0 != pre1;
  assert pre0 !in pre1.Repr();
  assert pre1 !in pre0.Repr();
  assert pre0.Repr() !! pre1.Repr();
}

// Compute n fibonacci prefixes of increasing length
method {:verify true} {:timelimitMultiplier 400} FibPrefixes(n: nat) returns (pres: List<List<nat>>)
  requires n >= 2

  ensures allocated(pres.Repr())
  ensures fresh(pres)
  ensures fresh(pres.Repr())
  ensures pres.Valid()
  ensures forall pre | pre in pres.Model() :: 
    && allocated(pre.Repr()) 
    && fresh(pre) 
    && fresh(pre.Repr()) 
    && pre.Valid() 
    
  ensures forall pre | pre in pres.Model() :: ({pres} + pres.Repr()) !! ({pre} + pre.Repr())
  ensures forall i, j | 0 <= i < j < |pres.Model()| ::
      ({pres.Model()[i]}+ pres.Model()[i].Repr()) !! ({pres.Model()[j]}+pres.Model()[j].Repr())

  ensures |pres.Model()| == n
  //ensures forall i | 0 <= i < |pres.Model()| ::
  //  pres.Model()[i].Model() == Fib(i+1)
{
  pres := FibPrefixes2();
  var i := 2;
  while i < n
    invariant allocated(pres.Repr())
    invariant fresh(pres)
    invariant fresh(pres.Repr())
    invariant pres.Valid()
    invariant forall pre | pre in pres.Model() ::
      && allocated(pre.Repr())
      && fresh(pre)
      && fresh(pre.Repr())
      && pre.Valid()
    invariant forall pre | pre in pres.Model() :: ({pres} + pres.Repr()) !! ({pre} + pre.Repr())
    invariant forall j, k | 0 <= j < k < |pres.Model()| ::
      ({pres.Model()[j]}+ pres.Model()[j].Repr()) !! ({pres.Model()[k]}+pres.Model()[k].Repr())

    invariant 2 <= i <= n
    invariant i == |pres.Model()|
    invariant forall i | 0 <= i < |pres.Model()| ::
      pres.Model()[i].Model() == Fib(i+1)
  {

    assert pres.Model()[|pres.Model()|-1] in pres.Model();

    assert forall pre | pre in pres.Model() ::
      && allocated(pre.Repr())
      && fresh(pre)
      && fresh(pre.Repr())
      && pre.Valid();
    assert pres.Model()[|pres.Model()|-1].Model()==Fib(|pres.Model()|);

    var lpre := pres.Back();

    assume forall pre | pre in pres.Model() ::
      && allocated(pre.Repr())
      && fresh(pre)
      && fresh(pre.Repr())
      && pre.Valid();
    assert lpre==pres.Model()[|pres.Model()|-1];
    assert lpre.Model() == Fib(|pres.Model()|);
    
    var npre := Copy(lpre);
    
    assert npre.Model() == Fib(i);

    NextPrefix(npre, i);
    
    assert allocated(npre.Repr());
    assert fresh(npre);
    assert fresh(npre.Repr());
    assert npre.Valid();
    assert npre.Model() == Fib(i+1);
   /* assert forall i | 0 <= i < |pres.Model()| ::
      pres.Model()[i].Model() == Fib(i+1);*/  
    assume allocated(pres.Repr()) && pres.Valid();

    assume forall pre | pre in pres.Model() ::
      && allocated(pre.Repr())
      && fresh(pre)
      && fresh(pre.Repr())
      && pre.Valid();
    assume ({pres}+pres.Repr()) !! ({npre}+npre.Repr());
    assume forall pre | pre in pres.Model() :: ({npre}+npre.Repr()) !! ({pre} + pre.Repr());
    assume forall j,k | 0 <= j < k < |pres.Model()| ::
      ({pres.Model()[j]}+ pres.Model()[j].Repr()) !! ({pres.Model()[k]}+pres.Model()[k].Repr());
    
    pres.PushBack(npre);
    i := i + 1;
    assume allocated(pres.Repr());
    assume fresh(pres);
    assume fresh(pres.Repr());
    assume pres.Valid();
    assume forall pre | pre in pres.Model() ::
      && allocated(pre.Repr())
      && fresh(pre)
      && fresh(pre.Repr())
      && pre.Valid();
    assume forall pre | pre in pres.Model() :: ({pres} + pres.Repr()) !! ({pre} + pre.Repr());
    assume forall j, k | 0 <= j < k < |pres.Model()| ::
      ({pres.Model()[j]}+ pres.Model()[j].Repr()) !! ({pres.Model()[k]}+pres.Model()[k].Repr());

  }
  assert i == n;
}

}
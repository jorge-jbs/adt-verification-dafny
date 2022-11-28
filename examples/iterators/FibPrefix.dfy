// Must be verified with -allocated:2

include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer3/LinkedListImpl.dfy"

function Fib(n: nat): seq<nat>
  ensures |Fib(n)| == n
{
  if n <= 2 then
    [0, 1][..n]
  else
    var fib := Fib(n-1);
    fib + [fib[n-3] + fib[n-2]]
}

predicate ValidDistinct(adts: seq<ADT>)
  reads set r | r in adts :: r
  reads BigUnion(set r | r in adts :: r.Repr())
{
  && (forall r | r in adts :: r.Valid())
  && (forall r, s | r in adts && s in adts && [r, s] <= adts ::
        {r} + r.Repr() !! {s} + s.Repr())
}

method NextPrefix(pre: List<nat>, n: nat)
  modifies pre, pre.Repr()
  requires allocated(pre.Repr())
  ensures fresh(pre.Repr()-old(pre.Repr()))
  requires ValidDistinct([pre])
  ensures ValidDistinct([pre])

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

method Copy<A>(l: List<A>) returns (nl: List<A>)  // 49.9s
  modifies l, l.Repr()
  requires allocated(l.Repr())
  ensures allocated(l.Repr())
  ensures fresh(l.Repr() - old(l.Repr()))
  ensures fresh(nl)
  ensures fresh(nl.Repr())

  requires ValidDistinct([l])
  ensures ValidDistinct([l, nl])

  ensures l.Model() == old(l.Model())
  ensures nl.Model() == l.Model()
{
  nl := new LinkedListImpl();
  assert forall r, s | [r, s] <= [l, nl] :: [r, s] == [l, nl];
  assert ValidDistinct([l, nl]);
  var it := l.Begin();
  var b := it.HasNext();
  while b
    decreases |l.Model()| - it.Index()
    invariant allocated(l.Repr())
    invariant fresh(l.Repr() - old(l.Repr()))
    invariant fresh(nl)
    invariant fresh(nl.Repr())

    invariant ValidDistinct([l, nl])
    invariant it.Valid()
    invariant it.Parent() == l
    invariant b == it.HasNext?()

    invariant l.Model() == old(l.Model())
    invariant nl.Model() == l.Model()[..it.Index()]
  {
    var x := it.Next();
    nl.PushBack(x);
    b := it.HasNext();
  }
}

method FibPrefixes2() returns (pres: List<List<nat>>)  // 45s
  ensures allocated(pres.Repr())
  ensures fresh(pres)
  ensures fresh(pres.Repr())
  ensures ValidDistinct([pres])
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
method FibPrefixes(n: nat) returns (pres: List<List<nat>>)
  requires n >= 2

  ensures allocated(pres.Repr())
  ensures fresh(pres)
  ensures fresh(pres.Repr())
  ensures ValidDistinct([pres])
  ensures forall pre | pre in pres.Model() :: allocated(pres.Repr())
  ensures forall r | r in pres.Model() :: r.Valid()
  ensures forall i, j | 0 <= i < j < |pres.Model()| ::
    && pres.Model()[i] != pres.Model()[j]
    && pres.Model()[i] !in pres.Model()[j].Repr()
    && pres.Model()[j] !in pres.Model()[i].Repr()
    && pres.Model()[i].Repr() !! pres.Model()[j].Repr()
  ensures forall pre | pre in pres.Model() :: pres.Repr() !! pre.Repr()

  ensures |pres.Model()| == n
  ensures forall i | 0 <= i < |pres.Model()| ::
    pres.Model()[i].Model() == Fib(i+1)
{
  pres := FibPrefixes2();
  var i := 2;
  while i < n
    invariant allocated(pres.Repr())
    invariant fresh(pres)
    invariant fresh(pres.Repr())
    invariant ValidDistinct([pres])
    invariant forall pre | pre in pres.Model() ::
      && allocated(pre.Repr())
      && fresh(pre)
      && fresh(pre.Repr())
    invariant forall pre | pre in pres.Model() :: {pres} + pres.Repr() !! {pre} + pre.Repr()
    invariant forall r | r in pres.Model() :: r.Valid()
    invariant forall i, j | 0 <= i < j < |pres.Model()| ::
      && pres.Model()[i] != pres.Model()[j]
      && pres.Model()[i] !in pres.Model()[j].Repr()
      && pres.Model()[j] !in pres.Model()[i].Repr()
      && pres.Model()[i].Repr() !! pres.Model()[j].Repr()

    invariant 2 <= i <= n
    invariant i == |pres.Model()|
    invariant forall i | 0 <= i < |pres.Model()| ::
      pres.Model()[i].Model() == Fib(i+1)
  {
    assert pres.Model()[|pres.Model()|-1] in pres.Model();
    label init:
    var lpre := pres.Back();
    var npre := Copy(lpre);
    NextPrefix(npre, i);
    assert forall i | 0 <= i < |pres.Model()| ::
      pres.Model()[i].Model() == Fib(i+1);
    assert npre.Model() == Fib(i+1);
    assert allocated(npre.Repr());
    assert fresh(npre);
    assert fresh(npre.Repr());
    assert {pres} + pres.Repr() !! {npre} + npre.Repr();
    assert npre.Valid();
    assert forall i | 0 <= i < |pres.Model()| ::
      && pres.Model()[i] != npre
      && pres.Model()[i] !in npre.Repr()
      && npre !in pres.Model()[i].Repr()
      && pres.Model()[i].Repr() !! npre.Repr();
    pres.PushBack(npre);
    i := i + 1;
  }
  assert i == n;
}

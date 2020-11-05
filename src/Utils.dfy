function method BigUnion<A>(S: set<set<A>>): set<A>
{
  set X, x | X in S && x in X :: x
}

module Array {
  function method elems<A>(l: array<A>): set<A>
    reads l
  {
    set x | x in l[..]
  }
}

module Seq {
  function Rev<A>(xs: seq<A>): seq<A>
  {
    if |xs| == 0 then
      []
    else
      Rev(xs[1..]) + [xs[0]]
  }

  function Map<A,B>(f: A -> B, xs: seq<A>): seq<B>
    reads (set x: A, o: object | x in xs && o in f.reads(x) :: o)
  {
    if xs == [] then
      []
    else
      [f(xs[0])] + Map(f, xs[1..])
  }

  function Elems<A>(xs: seq<A>): set<A>
  {
    set x | x in xs
  }

  lemma InEquivInMultiset<A>(xs: seq<A>)
    ensures forall x :: x in xs <==> x in multiset(xs)
  {}

  function Insert<A>(x: A, xs: seq<A>, i: nat): seq<A>
    requires 0 <= i <= |xs|
    ensures i == 0 ==> Insert(x, xs, i) == [x] + xs
    ensures i == |xs| ==> Insert(x, xs, i) == xs + [x]
  {
    xs[..i] + [x] + xs[i..]
  }

  function Remove<A>(xs: seq<A>, i: nat): seq<A>
    requires 0 <= i < |xs|
    ensures i == 0 ==> Remove(xs, i) == xs[1..]
    ensures i == |xs| ==> Remove(xs, i) == xs[..|xs|-1]
  {
    xs[..i] + xs[i+1..]
  }
}

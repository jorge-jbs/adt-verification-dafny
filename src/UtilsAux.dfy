lemma freshness1(x: set<object>, z: set<object>)
  ensures (forall y {:trigger y in x, y in z} | y in x - z :: fresh(y)) <==>
          (forall y | y in x && y !in z :: fresh(y))
{}

lemma freshness2(x: set<object>, z: set<object>)
  ensures (forall y | y in x - z :: fresh(y)) <==> (forall y | y in x && y !in z :: fresh(y))
{
  assume forall y | y in x - z :: fresh(y);
  forall y: object | y in x && y !in z
    ensures fresh(y)
  {
    assert y in x - z;
  }
  assert forall y | y in x && y !in z :: fresh(y);
}

lemma freshness3(x: set<object>, z: set<object>)
  ensures (forall y | y in x - z :: fresh(y)) <==> fresh(x-z)
{
  assume  (forall y | y in x - z :: fresh(y));
  forall y: object | y in x && y !in z
    ensures fresh(y)
  {
    assert y in x-z;
  }
}


module Seq {
  function FilterR<A>(xs: seq<A>,f: A -> bool): seq<A>
    ensures xs==[] ==> FilterR(xs,f) == xs
    ensures xs!=[] && f(xs[|xs|-1]) ==> FilterR(xs, f) == FilterR(xs[..|xs|-1], f)+[xs[|xs|-1]]
    ensures xs!=[] && !f(xs[|xs|-1]) ==> FilterR(xs, f) == FilterR(xs[..|xs|-1], f)
    ensures forall i :: 0 <= i < |FilterR(xs, f)| ==> f(FilterR(xs, f)[i])
  {
    if xs == [] then
      []
    else if f(xs[|xs|-1]) then
      FilterR(xs[..|xs|-1],f)+[xs[|xs|-1]]
    else
      FilterR(xs[..|xs|-1],f)
  }

  // This is the map that proves the subsequence property
  function FilterRMap<A>(xs: seq<A>, f: A -> bool): map<int, int>
  {
    if (xs == []) then map[]
    else if f(xs[|xs|-1]) then FilterRMap(xs[..|xs|-1],f)[|FilterR(xs,f)|-1 := |xs|-1]
    else FilterRMap(xs[..|xs|-1], f)
  }

  lemma subSecFilter<A>(xs: seq<A>,f: A -> bool)
    ensures subSec(FilterR(xs, f), xs, FilterRMap(xs, f))
  {
    if xs == [] {
    } else {
      var m := FilterRMap(xs[..|xs|-1], f);
      var filter:=FilterR(xs[..|xs|-1], f);
      assert subSec(filter,xs[..|xs|-1], m);
      assert |xs[..|xs|-1]| == |xs|-1;
      assert forall i :: 0 <= i < |filter| <==> i in m;
      assert forall i :: i in m ==> 0 <= m[i] < |xs|-1 && filter[i] == xs[..|xs|-1][m[i]];
      assert forall i, j :: i in m && j in m && i != j ==> m[i] != m[j];
      if f(xs[|xs|-1]) {
        assert |FilterR(xs,f)| == 1 + |filter|;
        assert forall i :: 0 <= i < |FilterR(xs,f)| <==> i in m[|FilterR(xs,f)|-1 := |xs|-1];
        assert forall i :: i in m[|FilterR(xs,f)|-1:=|xs|-1] ==>
             0 <= m[|FilterR(xs,f)|-1 := |xs|-1][i] < |xs| &&
             xs[m[|FilterR(xs,f)|-1 := |xs|-1][i]] == FilterR(xs,f)[i];
        forall i, j | i in m[|FilterR(xs,f)|-1 := |xs|-1] && j in m[|FilterR(xs,f)|-1 := |xs|-1] && i!=j
          ensures m[|FilterR(xs,f)|-1 := |xs|-1][i] != m[|FilterR(xs,f)|-1 := |xs|-1][j]
        {}
        assert subSec(FilterR(xs, f), xs, m[|FilterR(xs,f)|-1 := |xs| - 1]);
      } else {
      }
    }
  }

  lemma PropFilter<A>(xs: seq<A>,f: A -> bool)
    requires forall i :: 0 <= i < |xs| && f(xs[i]) ==> xs[i] in FilterR(xs,f)
    ensures isSubSec(FilterR(xs, f), xs)
  {
    subSecFilter(xs, f);
  }

  function FilterL<A>(xs: seq<A>,f: A -> bool): seq<A>
    ensures xs==[] ==> FilterL(xs,f) == xs
    ensures xs!=[] && f(xs[0]) ==> FilterL(xs,f)== [xs[0]]+FilterL(xs[1..],f)
    ensures xs!=[] && !f(xs[0]) ==> FilterL(xs,f)== FilterL(xs[1..],f)
    ensures forall i::0<=i<|FilterL(xs,f)| ==> f(FilterL(xs,f)[i])
  {
    if xs==[] then []
    else if f(xs[0]) then [xs[0]]+FilterL(xs[1..],f)
    else FilterL(xs[1..],f)
  }

  // TODO
  lemma filter<A>(xs: seq<A>, f: A -> bool)
    ensures FilterR(xs,f) == FilterL(xs,f)

  predicate Sorted(xs: seq<int>)
  {
    forall i, j :: 0 <= i <= j < |xs| ==> xs[i] <= xs[j]
  }

  predicate StrictSorted(xs: seq<int>)
  {
    forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]
  }

  predicate subSec<A>(xs1: seq<A>, xs2: seq<A>, f: map<int, int>)
  {
    && (forall i :: (0 <= i < |xs1| <==> i in f))
    && (forall i :: i in f ==> 0 <= i < |xs1| && 0 <= f[i] < |xs2| && xs2[f[i]] == xs1[i])
    && (forall i, j :: i in f && j in f && i!=j ==> f[i]!=f[j])
  }

  predicate isSubSec<A>(xs1: seq<A>, xs2: seq<A>)
  {
    exists f: map<int, int> :: subSec(xs1, xs2, f)
  }
}

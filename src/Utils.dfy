function method BigUnion<A>(S: set<set<A>>): set<A>
{
  set X, x | X in S && x in X :: x
}

function method abs(x: int): int
{
  if x < 0 then
    -x
  else
    x
}

lemma reprProgression<A>(s1: set<A>, s2: set<A>, s3: set<A>)
  requires (s3-s2) * s1 == {} // s3-s2 is completely fresh respect s1
  ensures s3-s1 == (s3-s2) + (s2-s1) * s3
{
  if s1 == {} || s3 == {} || s2 == {}
    {}
  else {
    assert s3-s1==(s3-s2)+(s2-s1)*s3-(s3-s2)*s1;
    assert (s3-s2)*s1=={};
  }
}

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


module Array {
  function method elems<A>(l: array<A>): set<A>
    reads l
  {
    set x | x in l[..]
  }

  function method melems<A>(l: array<A>): multiset<A>
    reads l
  {
    multiset(l[..])
  }
}

module Seq {
  function Rev<A>(xs: seq<A>): seq<A>
    ensures |xs| == |Rev(xs)|
  {
    if |xs| == 0 then
      []
    else
      Rev(xs[1..]) + [xs[0]]
  }

  lemma LastRev<A>(xs: seq<A>)
    requires |xs| > 0
    ensures Rev(xs) == [xs[|xs|-1]] + Rev(xs[..|xs|-1])
  {
    if |xs| == 0 {
    } else if |xs| == 1 {
    } else {
      calc == {
        Rev(xs);
        Rev([xs[0]] + xs[1..]);
        Rev(xs[1..]) + [xs[0]];
        { LastRev(xs[1..]); }
        [xs[|xs|-1]] + Rev(xs[1..][..|xs[1..]|-1]) + [xs[0]];
        { assert xs[1..][..|xs[1..]|-1] == xs[1..|xs|-1]; }
        [xs[|xs|-1]] + Rev(xs[1..|xs|-1]) + [xs[0]];
        [xs[|xs|-1]] + Rev([xs[0]] + xs[1..|xs|-1]);
        [xs[|xs|-1]] + Rev(xs[..|xs|-1]);
      }
    }
  }

  lemma LeRev(xs: seq<int>)
    requires forall i | 0 <= i < |xs|-1 :: xs[i] >= xs[i+1]
    ensures forall i | 0 <= i < |xs|-1 :: Rev(xs)[i] <= Rev(xs)[i+1]
  {}

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

  lemma ElemsRev<A>(l: seq<A>)
    ensures Elems(Rev(l)) == Elems(l)
    ensures forall x | x in Rev(l) :: x in l
    ensures forall x | x in l :: x in Rev(l)
  {
    if |l| == 0 {
    } else {
      ElemsRev(l[1..]);
      assert Elems(Rev(l[1..])) == Elems(l[1..]);
      calc == {
        Elems(Rev(l));
        { assert [l[0]] + l[1..] == l; }
        Elems(Rev([l[0]] + l[1..]));
        Elems(Rev(l[1..]) + [l[0]]);
        Elems(Rev(l[1..])) + Elems([l[0]]);
        Elems(l);
      }
    }
  }

  lemma MElemsRev<A>(l: seq<A>)
    ensures MElems(Rev(l)) == MElems(l)
  {
    if |l| == 0 {
    } else {
      MElemsRev(l[1..]);
      assert [l[0]] + l[1..] == l;
    }
  }

  function MElems<A>(xs: seq<A>): multiset<A>
  {
    multiset(xs)
  }

  lemma InEquivInMultiset<A>(xs: seq<A>)
    ensures forall x :: x in xs <==> x in multiset(xs)
  {}

  function Insert<A>(x: A, xs: seq<A>, i: nat): seq<A>
    requires 0 <= i <= |xs|
    ensures |xs| + 1 == |Insert(x, xs, i)|
    ensures i == 0 ==> Insert(x, xs, i) == [x] + xs
    ensures i == |xs| ==> Insert(x, xs, i) == xs + [x]
    ensures Insert(x, xs, i)[i] == x
    ensures forall k | 0 <= k < i :: xs[k] == Insert(x, xs, i)[k]
    ensures forall k | i <= k < |xs| :: xs[k] == Insert(x, xs, i)[k+1]
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

module Set {
  ghost function BigUnion<A>(S: set<set<A>>): set<A>
  {
    set X, x | X in S && x in X :: x
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

  lemma SubsetCard<A>(s: set<A>, S: set<A>)
    requires s <= S
    ensures |s| <= |S|
  {
    if s == S {
    } else {
      var x :| x in S-s;
      SubsetCard(s, S - {x});
    }
  }

  lemma StrictSubsetCard<A>(s: set<A>, S: set<A>)
    requires s < S
    ensures |s| < |S|
  {
    var x :| x in S-s;
    SubsetCard(s, S - {x});
  }

  lemma AddCard<A>(r: set<A>, s: set<A>)
    requires r !! s
    ensures |r + s| == |r| + |s|
  {}

  lemma SubCard<A>(r: set<A>, s: set<A>)
    requires s <= r
    ensures |r - s| == |r| - |s|
  {}
}

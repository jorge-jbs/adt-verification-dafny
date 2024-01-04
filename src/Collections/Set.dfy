module  Set {
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

  lemma Allocated(s: set<object>)
    ensures allocated(s)
  {}

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

  lemma AddCard<A>(r: set<A>, s: set<A>)
    requires r !! s
    ensures |r + s| == |r| + |s|
  {}

  lemma SubCard<A>(r: set<A>, s: set<A>)
    requires s <= r
    ensures |r - s| == |r| - |s|
  {}
}

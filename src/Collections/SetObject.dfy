module SetObject {
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
    if forall y | y in x - z :: fresh(y) {
      forall y: object | y in x && y !in z
        ensures fresh(y)
      {
        assert y in x - z;
      }
      assert forall y | y in x && y !in z :: fresh(y);
    }
  }
}

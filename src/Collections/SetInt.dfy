include "../Collections/Set.dfy"

module SetInt {
  import opened Set

  function Filter(P: int -> bool, s: set<int>): set<int>
  {
    set x <- s | P(x)
  }

  function Smaller(s: set<int>, x: int): set<int>
    //ensures Smaller(s, x) == Filter(y => y < x, s)
  {
    set z <- s | z < x
  }

  predicate SmallerSubset(s: set<int>, S: set<int>)
  {
    forall x <- s, y <- S-s :: x < y
  }

  predicate IsMin(s: set<int>, x: int)
  {
    && x in s
    && forall y <- s :: x <= y
  }

  lemma MinUnique(s: set<int>, x: int, y: int)
    requires x in s
    requires y in s
    requires IsMin(s, x)
    requires IsMin(s, y)
    ensures x == y
  {}

/*
  ghost function GMin(s: set<int>): int
    requires s != {}
    //ensures IsMin(s, GMin(s))
  {
    var x :| x in s;
    if s - {x} == {} then
      x
    else if x < GMin(s - {x}) then
      x
    else
      GMin(s - {x})
  }
  */

  lemma MinConstruct(s: set<int>) returns (min: int)
    requires s != {}
    ensures IsMin(s, min)
    ensures forall x <- s | IsMin(s, x) :: x == min
  {
    var x :| x in s;
    if s - {x} == {} {
      assert s == {x};
      return x;
    } else {
      var min' := MinConstruct(s - {x});
      if x < min' {
        forall y | y in s
          ensures x <= y
        {
          if x == y {
          } else {
            assert y in s - {x};
            assert x < min' <= y;
          }
        }
        return x;
      } else {
        forall y | y in s
          ensures min' <= y
        {
          if y == x {
          } else {
            assert y in s - {x};
          }
        }
        return min';
      }
    }
  }

  lemma MinExists(s: set<int>)
    requires s != {}
    ensures exists min ::
      && IsMin(s, min)
      && forall x <- s | IsMin(s, x) :: x == min
  {
    var min := MinConstruct(s);
  }

  function Min(s: set<int>): int
    requires s != {}
  {
    MinExists(s);
    var x :| IsMin(s, x);
    x
  }


  predicate IsMax(s: set<int>, x: int)
  {
    && x in s
    && forall y <- s :: y <= x
  }

  lemma MaxUnique(s: set<int>, x: int, y: int)
    requires x in s
    requires y in s
    requires IsMax(s, x)
    requires IsMax(s, y)
    ensures x == y
  {}

  lemma MaxConstruct(s: set<int>) returns (max: int)
    requires s != {}
    ensures IsMax(s, max)
    ensures forall x <- s | IsMax(s, x) :: x == max
  {
    var x :| x in s;
    if s - {x} == {} {
      assert s == {x};
      return x;
    } else {
      var max' := MaxConstruct(s - {x});
      if max' < x {
        forall y | y in s
          ensures y <= x
        {
          if x == y {
          } else {
            assert y in s - {x};
            assert y <= max' < x;
          }
        }
        return x;
      } else {
        forall y | y in s
          ensures y <= max'
        {
          if y == x {
          } else {
            assert y in s - {x};
          }
        }
        return max';
      }
    }
  }

  lemma MaxExists(s: set<int>)
    requires s != {}
    ensures exists max ::
      && IsMax(s, max)
      && forall x <- s | IsMax(s, x) :: x == max
  {
    var max := MaxConstruct(s);
  }

  function Max(s: set<int>): int
    requires s != {}
  {
    MaxExists(s);
    var x :| IsMax(s, x);
    x
  }

  function ElemAt(s: set<int>, i: nat): int
    requires 0 <= i < |s|
  {
    var m := Min(s);
    if i == 0 then
      m
    else
      ElemAt(s - {m}, i - 1)
  }

  lemma ElemAtInSet(s: set<int>, i: nat)
    requires 0 <= i < |s|
    ensures ElemAt(s, i) in s
  {}

  lemma SmallerElemAt(s: set<int>, i: int)
    requires 0 <= i < |s|
    ensures |Smaller(s, ElemAt(s, i))| == i
  {
    var m := Min(s);
    if i == 0 {
    } else {
      SmallerElemAt(s - {m}, i-1);
      assert |Smaller(s - {m}, ElemAt(s - {m}, i-1))| == i-1;
      calc =={
        |Smaller(s, ElemAt(s, i))|;
        |set z <- s | z < ElemAt(s, i)|;
        { assert i > 0; }
        |set z <- s | z < ElemAt(s - {m}, i-1)|;
        {
          assert s == (s - {m}) + {m};
          var elemAt := ElemAt(s - {m}, i-1);
          assert m < elemAt;
          assert (set z <- s | z < elemAt) == (set z <- s - {m} | z < elemAt) + {m};
        }
        |(set z <- s - {m} | z < ElemAt(s - {m}, i-1)) + {m}|;
        |Smaller(s - {m}, ElemAt(s - {m}, i-1)) + {m}|;
        |Smaller(s - {m}, ElemAt(s - {m}, i-1))| + 1;
        (i-1) + 1;
        i;
      }
    }
  }

  lemma ElemAtIsMinOfComplement(s: set<int>, S: set<int>)
    decreases S
    requires s < S
    requires SmallerSubset(s, S)
    ensures |s| < |S|
    ensures S-s != {}
    ensures ElemAt(S, |s|) == Min(S-s)
  {
    assert |s| < |S| by {
      StrictSubsetCard(s, S);
    }
    assert ElemAt(S, |s|) in S by {
      ElemAtInSet(S, |s|);
    }
    assert S-s != {} by {
      assert s != S;
      var x :| x in S && x !in s;
      assert x in S-s;
    }
    if s == {} {
      calc == {
        ElemAt(S, |s|);
        ElemAt(S, 0);
        { assert S == S - {}; }
        ElemAt(S-{}, 0);
        ElemAt(S-s, 0);
        Min(S-s);
      }
    } else {
      var m := Min(S);
      assert m in S;
      assert m in s by {
        if m !in s {
          assert m in S-s;
          assert forall y <- s :: y < m;
          var y :| y in s && y < m;
        }
      }
      assert m !in S-s;
      assert s-{m} < S-{m} by {
        assert s-{m} <= S-{m};
        assert s-{m} != S-{m};
        var z :| z in S-s;
        assert z != m;
      }
      assert SmallerSubset(s-{m}, S-{m}) by {
        assert (S-{m})-(s-{m}) == S-s;
        assert forall x <- s-{m}, y <- (S-{m})-(s-{m}) :: x < y;
      }

      calc == {
        ElemAt(S, |s|);
        ElemAt(S-{m}, |s|-1);
        ElemAt(S-{m}, |s-{m}|);
        {
          assert ElemAt(S-{m}, |s-{m}|) == Min((S-{m})-(s-{m})) by {
            ElemAtIsMinOfComplement(s-{m}, S-{m});
          }
        }
        Min((S-{m})-(s-{m}));
        { assert (S-{m})-(s-{m}) == S-s; }
        Min(S-s);
      }
    }
  }

  lemma ElemAtNotInSmallerSubset(s: set<int>, S: set<int>)
    decreases S-s
    requires s < S
    requires SmallerSubset(s, S)
    ensures |s| < |S|
    ensures ElemAt(S, |s|) in S
    ensures ElemAt(S, |s|) !in s
  {
    ElemAtIsMinOfComplement(s, S);
  }
}

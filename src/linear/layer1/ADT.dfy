trait ADT<M> {
  ghost const ReprDepth: nat

  function ReprFamily(n: nat): set<object>
    decreases n
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)

  function Repr(): set<object>
    reads this, if ReprDepth == 0 then {} else ReprFamily(ReprDepth-1)
  {
    ReprFamily(ReprDepth)
  }

  predicate Valid()
    reads this, Repr()

  function Model(): M
    reads this, Repr()
    requires Valid()
}
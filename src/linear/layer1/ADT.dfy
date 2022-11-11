type pos = n: int | n > 0 witness 1

trait ADT<M> {
  ghost const ReprDepth: pos

  function ReprFamily(n: nat): set<object>
    decreases n
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)

  function Repr(): set<object>
    reads this, ReprFamily(ReprDepth-1)
  {
    ReprFamily(ReprDepth)
  }

  predicate Valid()
    reads this, Repr()

  function Model(): M
    reads this, Repr()
    requires Valid()
}
include "../../../src/Utils.dfy"

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

  predicate ValidDistinct(adts: seq<ADT>)
  reads set r | r in adts :: r
  reads BigUnion(set r | r in adts :: r.Repr())
{
  && (forall r | r in adts :: r.Valid())
  && (forall r, s | r in adts && s in adts && [r, s] <= adts ::
        {r} + r.Repr() !! {s} + s.Repr())
}
}
include "../src/Utils.dfy"

type pos = n: int | n > 0 witness 1

trait ADT<M> {
  ghost const ReprDepth: pos

  ghost function ReprFamily(n: nat): set<object>
    decreases n
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)

  ghost function Repr(): set<object>
    reads this, ReprFamily(ReprDepth-1)
  {
    ReprFamily(ReprDepth)
  }

  ghost predicate Valid()
    reads this, Repr()

  ghost function Model(): M
    reads this, Repr()
    requires Valid()
}

ghost predicate ValidDistinctADTs(adts: seq<ADT>)
  reads set r | r in adts :: r
  reads Set.BigUnion(set r | r in adts :: r.Repr())
  {
    && (forall r | r in adts :: r.Valid())
    && (forall r, s | r in adts && s in adts && [r, s] <= adts ::
        {r} + r.Repr() !! {s} + s.Repr())
  }
ghost predicate ValidDistinctObjs(objects: seq<object>)
  {
    forall r, s | r in objects && s in objects && [r, s] <= objects ::
        {r}  !! {s} 
  }

ghost predicate ValidDistinct(adts: seq<ADT>, objs: seq<object>)
  reads set r | r in adts :: r
  reads Set.BigUnion(set r | r in adts :: r.Repr())
  {
   && (forall r | r in adts :: r.Valid())
   && (forall r, s | r in adts && s in adts && [r, s] <= adts ::
         {r} + r.Repr() !! {s} + s.Repr())
   && (forall r, s | r in objs && s in objs && [r, s] <= objs ::
         {r} !! {s})
   && (forall r, s | r in adts && s in objs ::
         {r} + r.Repr() !! {s})
  }

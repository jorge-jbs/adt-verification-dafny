include "Collections/Set.dfy"
include "Collections/SetObject.dfy"

module ADT {
  import opened Set
  import opened SetObject

  type pos = n: int | n > 0 witness 1

  trait {:termination false} ADT<M> {
    ghost const ReprDepth: pos

    ghost function ReprFamily(n: nat): set<object>
      decreases n
      //ensures forall i, j | 0 <= i < j <= n :: ReprFamily(i) <= ReprFamily(j)
      ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
      reads this, if n == 0 then {} else ReprFamily(n-1)

    ghost function Repr(): set<object>
      reads this, ReprFamily(ReprDepth-1)
    {
      ReprFamily(ReprDepth)
    }

    lemma ReprLemma()
      ensures Repr() == ReprFamily(ReprDepth)
    {}

    ghost predicate Valid()
      reads this, Repr()

    ghost function Model(): M
      reads this, Repr()
      requires Valid()
  }

  datatype ADT2<A, B> = ADT2(a: ADT<A>, b: ADT<B>)
  {
    ghost function Repr(): set<object>
      reads a, a.ReprFamily(a.ReprDepth-1)
      reads b, b.ReprFamily(b.ReprDepth-1)
    {
      {a} + a.Repr() + {b} + b.Repr()
    }

    ghost predicate Valid()
      reads Repr()
      //reads a, a.Repr(), b, b.Repr()
      ensures Valid() ==> a.Valid()
      ensures Valid() ==> b.Valid()
    {
      && a.Valid()
      && b.Valid()
      //&& {a} + a.Repr() !! {b} + b.Repr()
      && a.Repr() !! b.Repr()
      && a !in b.Repr()
      && b !in a.Repr()
      && a != b
    }
  }

  ghost predicate Valid2<A, B>(a: ADT<A>, b: ADT<B>)
    reads a, a.Repr(), b, b.Repr()
    ensures Valid2(a, b) ==> a.Valid()
    ensures Valid2(a, b) ==> b.Valid()
  {
    && a.Valid()
    && b.Valid()
    //&& {a} + a.Repr() !! {b} + b.Repr()
    && a.Repr() !! b.Repr()
    && a !in b.Repr()
    && b !in a.Repr()
    && a != b
  }

  twostate predicate MaintainsValid2<A, B>(a: ADT<A>, b: ADT<B>)
    reads a, a.Repr(), b, b.Repr()
    requires old(Valid2(a, b))
  {
    && Valid2(a, b)
    && fresh(a.Repr() - old(a.Repr()))
    && fresh(b.Repr() - old(b.Repr()))
  }

  datatype ADT3<A, B, C> = ADT3(a: ADT<A>, b: ADT<B>, c: ADT<C>)
  {
    ghost function Repr(): set<object>
      reads a, a.ReprFamily(a.ReprDepth-1)
      reads b, b.ReprFamily(b.ReprDepth-1)
      reads c, c.ReprFamily(c.ReprDepth-1)
    {
      {a} + a.Repr() + {b} + b.Repr() + {c} + c.Repr()
    }

    twostate predicate Fresh()
      reads Repr()
    {
      && fresh(a.Repr() - old(a.Repr()))
      && fresh(b.Repr() - old(b.Repr()))
      && fresh(c.Repr() - old(c.Repr()))
    }

    ghost predicate {:inline} Valid()
      //reads a, a.Repr(), b, b.Repr(), c, c.Repr()
      reads Repr()
      ensures Valid() ==> a.Valid()
      ensures Valid() ==> b.Valid()
      ensures Valid() ==> c.Valid()
    {
      && a.Valid()
      && b.Valid()
      && c.Valid()

      //&& {a} + a.Repr() !! {b} + b.Repr()
      && a.Repr() !! b.Repr()
      && a !in b.Repr()
      && b !in a.Repr()
      && a != b

      //&& {a} + a.Repr() !! {c} + c.Repr()
      && a.Repr() !! c.Repr()
      && a !in c.Repr()
      && c !in a.Repr()
      && a != c

      //&& {b} + b.Repr() !! {c} + c.Repr()
      && b.Repr() !! c.Repr()
      && b !in c.Repr()
      && c !in b.Repr()
      && b != c
    }
  }

  twostate lemma MaintainsValid2Helper<A, B>(a: ADT<A>, b: ADT<B>)
    requires a.Valid()
    requires fresh(a.Repr() - old(a.Repr()))

    requires old(allocated(a.Repr()))
    requires old(allocated(b.Repr()))
    requires allocated(b.Repr())
    requires b.Repr() == old(b.Repr())
    requires unchanged({b} + b.Repr())

    //requires old(a.Repr()) !! b.Repr()
    requires old(Valid2(a, b))

    ensures MaintainsValid2(a, b)
    ensures allocated(a.Repr())
    ensures allocated(b.Repr())
  {
    //reveal Valid2();
  }

  ghost predicate Valid3<A, B, C>(a: ADT<A>, b: ADT<B>, c: ADT<C>)
    reads a, a.Repr(), b, b.Repr(), c, c.Repr()
    ensures Valid3(a, b, c) ==> a.Valid()
    ensures Valid3(a, b, c) ==> b.Valid()
    ensures Valid3(a, b, c) ==> c.Valid()
  {
    && a.Valid()
    && b.Valid()
    && c.Valid()

    //&& {a} + a.Repr() !! {b} + b.Repr()
    && a.Repr() !! b.Repr()
    && a !in b.Repr()
    && b !in a.Repr()
    && a != b

    //&& {a} + a.Repr() !! {c} + c.Repr()
    && a.Repr() !! c.Repr()
    && a !in c.Repr()
    && c !in a.Repr()
    && a != c

    //&& {b} + b.Repr() !! {c} + c.Repr()
    && b.Repr() !! c.Repr()
    && b !in c.Repr()
    && c !in b.Repr()
    && b != c
  }

  twostate lemma MaintainsValid3Helper<A, B, C>(a: ADT<A>, b: ADT<B>, c: ADT<C>)
    requires a.Valid()
    requires fresh(a.Repr() - old(a.Repr()))

    requires old(allocated(a.Repr()))
    requires old(allocated(b.Repr()))
    requires old(allocated(c.Repr()))
    requires allocated(b.Repr())
    requires allocated(c.Repr())
    requires b.Repr() == old(b.Repr())
    requires c.Repr() == old(c.Repr())
    requires unchanged({b} + b.Repr())
    requires unchanged({c} + c.Repr())

    requires old(Valid3(a, b, c))

    ensures Valid3(a, b, c)
    ensures fresh(a.Repr() - old(a.Repr()))
    ensures fresh(b.Repr() - old(b.Repr()))
    ensures fresh(c.Repr() - old(c.Repr()))
    ensures allocated(a.Repr())
    ensures allocated(b.Repr())
    ensures allocated(c.Repr())
  {
  }

  ghost predicate ValidDistinctADTs(adts: seq<ADT>)
    reads set r | r in adts :: r
    reads BigUnion(set r | r in adts :: r.Repr())
  {
    && (forall r | r in adts :: r.Valid())
    && (forall r, s | r in adts && s in adts && [r, s] <= adts ::
          {r} + r.Repr() !! {s} + s.Repr())
  }

  ghost predicate ValidDistinctObjs(objects: seq<object>)
  {
    forall r, s | r in objects && s in objects && [r, s] <= objects ::
      {r} !! {s}
  }

  ghost predicate ValidDistinct(adts: seq<ADT>, objs: seq<object>)
    reads set r | r in adts :: r
    reads BigUnion(set r | r in adts :: r.Repr())
  {
    && (forall r | r in adts :: r.Valid())
    && (forall r, s | r in adts && s in adts && [r, s] <= adts ::
          {r} + r.Repr() !! {s} + s.Repr())
    && (forall r, s | r in objs && s in objs && [r, s] <= objs ::
          {r} !! {s})
    && (forall r, s | r in adts && s in objs ::
          {r} + r.Repr() !! {s})
  }

  twostate lemma Disjoint(new r: set<object>, rr: set<object>, s: set<object>)
    requires fresh(r - rr)
    //requires unchanged(s)
    requires rr !! s
    ensures r !! s
  {}

/*
  twostate lemma DisjointFromFresh(x: ADT, y: ADT)
    requires old(allocated({x} + x.Repr()))
    requires old(allocated({y} + y.Repr()))
    requires allocated({x} + x.Repr())
    requires allocated({y} + y.Repr())
    requires fresh(x.Repr() - old(x.Repr()))
    requires fresh(y.Repr() - old(y.Repr()))
    requires old({x} + x.Repr() !! {y} + y.Repr())
    ensures {x} + x.Repr() !! {y} + y.Repr()
  {
    assert allocated(old(y.Repr()));
    assert old(allocated(y.Repr()));
    assert allocated(y.Repr());
    assume unchanged(y);
    assume unchanged(y.Repr());
    assume unchanged({y} + y.Repr());
  }
  */
}

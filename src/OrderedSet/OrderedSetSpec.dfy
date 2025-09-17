include "../../src/AdtWithoutThis.dfy"
include "../../src/Collections/KeyValue.dfy"
include "../../src/UnorderedSet/UnorderedSetSpec.dfy"

module OrderedSetSpec {
  import opened ADT
  import opened KeyValue
  import opened UnorderedSetSpec

  trait {:termination false} OrderedSetIterator extends UnorderedSetIterator {
    ghost function Parent(): UnorderedSet
      ensures Parent() is OrderedSet

    ghost predicate Valid()
      reads Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()

    opaque ghost predicate AfterSpec(after: set<K>)
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
    {
      && after < Parent().Model()
      && |after| < |Parent().Model()|
    }

    opaque ghost function After(): set<K>
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures AfterSpec(After())
    {
      var after := (Parent().Model() - {Peek?()})  - Before();
      assert AfterSpec(after) by { reveal AfterSpec(), PeekSpec(), BeforeSpec(); }
      after
    }

    opaque ghost predicate RTraversedSpec(rtraversed: set<K>)
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
    {
      && rtraversed <= Parent().Model()
      && |rtraversed| <= |Parent().Model()|
    }

    /*
    Helper function that specifies what elements have been traversed while
    iterating the set from front to back, by repeatedly calling `Prev` (backwards).

    It is, essentially, a total version of `After`.
    */
    ghost function RTraversed(): set<K>
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures RTraversedSpec(RTraversed())
    {
      if HasPeek?() then
        assert RTraversedSpec(After()) by { reveal RTraversedSpec(), AfterSpec(); }
        After()
      else
        assert RTraversedSpec(Parent().Model()) by { reveal RTraversedSpec(); }
        Parent().Model()
    }

    opaque ghost predicate PeekOrderSpec(p: K)
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
    {
      && (forall x <- Before() :: x < p)
      && (forall x <- Parent().Model() | x !in Before() :: p <= x)
    }

    lemma PeekROrder()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures forall x <- After() :: Peek?() < x
      ensures forall x <- Parent().Model() | x !in After() :: x <= Peek?()
    {
      reveal After();
      reveal PeekOrderSpec();
    }

    ghost function Peek?(): K
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures PeekSpec(Peek?())
      ensures PeekOrderSpec(Peek?())

    opaque twostate predicate PrevModel()
      reads Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
      requires old(HasPeek?())
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && RTraversed() == {old(Peek?())} + old(After())
      && |RTraversed()| == 1 + old(|After()|)
    }

    method Prev()
      modifies Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures PrevModel()
      ensures NextIterators()
  }

  trait {:termination false} OrderedSet extends UnorderedSet {
    ghost function Iterators(): set<UnorderedSetIterator>
      reads Repr()
      requires Valid()
      ensures forall it <- Iterators() ::
                && it in Repr()
                && it.Parent() == this
                && it is OrderedSetIterator

    opaque twostate predicate LastModel(new it: OrderedSetIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires it.Valid()
      requires it.Parent() == this
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && it.RTraversed() == {}
    }

    method Last() returns (it: OrderedSetIterator)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()

      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures Iterators() >= {it} + old(Iterators())

      ensures LastModel(it)
      ensures SameIterators()
  }

  ghost predicate ValidIt(s: OrderedSet, it: OrderedSetIterator)
    reads s.Repr()
    requires s.Valid()
  {
    && it.Parent() == s
    && it in s.Iterators()
    && it.Valid()
  }

  ghost predicate Valid1It1(s: OrderedSet, it: OrderedSetIterator)
    reads s.Repr()
  {
    s.Valid() && ValidIt(s, it)
  }

  ghost predicate Valid2It11(
    a: OrderedSet,
    itA: OrderedSetIterator,
    b: OrderedSet,
    itB: OrderedSetIterator
  )
    reads a.Repr(), b.Repr()
  {
    && Valid2(a, b)
    && ValidIt(a, itA)
    && ValidIt(b, itB)
  }

  twostate predicate MaintainsValid2It11(
    a: OrderedSet,
    itA: OrderedSetIterator,
    b: OrderedSet,
    itB: OrderedSetIterator
  )
    reads a.Repr(), b.Repr()
    requires old(Valid2It11(a, itA, b, itB))
  {
    && Valid2It11(a, itA, b, itB)
    && MaintainsValid2(a, b)
    && a.Iterators() >= old(a.Iterators())
    && b.Iterators() >= old(b.Iterators())
  }

  twostate lemma MaintainsValid2It11Helper(
    a: OrderedSet,
    itA: OrderedSetIterator,
    b: OrderedSet,
    itB: OrderedSetIterator
  )
    requires old(Valid2It11(a, itA, b, itB))

    requires a.Valid()
    requires ValidIt(a, itA)
    requires fresh(a.Repr() - old(a.Repr()))
    requires a.Iterators() >= old(a.Iterators())

    requires old(allocated(a.Repr()))
    requires old(allocated(b.Repr()))
    requires allocated(b.Repr())
    requires b.Repr() == old(b.Repr())
    requires unchanged(b.Repr())

    ensures MaintainsValid2It11(a, itA, b, itB)
    ensures allocated(a.Repr())
    ensures allocated(b.Repr())
  {}

  ghost predicate Valid3It100(
    a: OrderedSet,
    itA: OrderedSetIterator,
    b: OrderedSet,
    c: OrderedSet
  )
    reads a.Repr(), b.Repr(), c.Repr()
  {
    && Valid3(a, b, c)
    && ValidIt(a, itA)
  }

  ghost predicate Valid3It110(
    a: OrderedSet,
    itA: OrderedSetIterator,
    b: OrderedSet,
    itB: OrderedSetIterator,
    c: OrderedSet
  )
    reads a.Repr(), b.Repr(), c.Repr()
  {
    && Valid3(a, b, c)
    && ValidIt(a, itA)
    && ValidIt(b, itB)
  }

  twostate lemma MaintainsValid3It110Helper(
    a: OrderedSet,
    itA: OrderedSetIterator,
    b: OrderedSet,
    itB: OrderedSetIterator,
    c: OrderedSet
  )
    requires old(Valid3It110(a, itA, b, itB, c))

    requires a.Valid()
    requires ValidIt(a, itA)
    requires fresh(a.Repr() - old(a.Repr()))
    requires a.Iterators() >= old(a.Iterators())

    requires old(allocated(a.Repr()))
    requires old(allocated(b.Repr()))
    requires old(allocated(c.Repr()))
    requires allocated(b.Repr())
    requires allocated(c.Repr())
    requires b.Repr() == old(b.Repr())
    requires c.Repr() == old(c.Repr())
    requires unchanged(b.Repr())
    requires unchanged(c.Repr())

    ensures Valid3It110(a, itA, b, itB, c)
    ensures fresh(a.Repr() - old(a.Repr()))
    ensures fresh(b.Repr() - old(b.Repr()))
    ensures fresh(c.Repr() - old(c.Repr()))
    ensures a.Iterators() >= old(a.Iterators())
    ensures b.Iterators() >= old(b.Iterators())
    ensures c.Iterators() >= old(c.Iterators())
    ensures allocated(a.Repr())
    ensures allocated(b.Repr())
    ensures allocated(c.Repr())
  {}

  ghost predicate ValidIt2(
    a: OrderedSet,
    itA: OrderedSetIterator,
    itB: OrderedSetIterator
  )
    reads a, a.Repr()
  {
    && a.Valid()
    && ValidIt(a, itA)
    && ValidIt(a, itB)
  }
}
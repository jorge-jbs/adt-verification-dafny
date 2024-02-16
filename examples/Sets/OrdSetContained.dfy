include "../../src/OrderedSet/OrderedSetSpec.dfy"

module OrdSetContained {
  import opened OrderedSetSpec

  export provides OrderedSetSpec, OrdSetContained

  ghost predicate StaticInvariant(s1: OrderedSet, s2: OrderedSet)
    reads s1, s1.Repr(), s2, s2.Repr()
  {
    && s1.Valid() && s2.Valid()
    && {s1} + s1.Repr() !! {s2} + s2.Repr()
  }

  twostate predicate DynamicInvariant(s1: OrderedSet, s2: OrderedSet)
    reads s1, s1.Repr(), s2, s2.Repr()
    requires old(StaticInvariant(s1, s2))
    requires StaticInvariant(s1, s2)
  {
    && fresh(s1.Repr() - old(s1.Repr()))
    && fresh(s2.Repr() - old(s2.Repr()))
    && s1.Iterators() >= old(s1.Iterators())
    && s2.Iterators() >= old(s2.Iterators())
    && s1.Model() == old(s1.Model())
    && s2.Model() == old(s2.Model())
  }

  ghost predicate LoopInvariant(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      it1HasPeek: bool,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      it2HasPeek: bool,
      b: bool
    )
    reads s1, s1.Repr(), s2, s2.Repr(), it1, it2
  {
    && StaticInvariant(s1, s2)

    && it1.Parent() == s1 && it2.Parent() == s2
    && it1.Valid() && it2.Valid()
    && it1 in s1.Iterators() && it2 in s2.Iterators()
    && it1.Traversed() <= s1.Model() && it2.Traversed() <= s2.Model()
    && 0 <= it1.Index() <= |s1.Model()| && 0 <= it2.Index() <= |s2.Model()|
    //&& !it2.HasNext()==> b
    && (b ==> it1.Traversed() <= it2.Traversed())
    && (!b ==> !(it1.Traversed() <= s2.Model()))
    && (it1.HasPeek?() ==> it1.Peek?() !in it2.Traversed())
    && (forall u | u in it2.Traversed() && it1.Traversed() < s1.Model() :: u < it1.Peek?())

    && it1HasPeek == it1.HasPeek?()
    && it2HasPeek == it2.HasPeek?()
  }

  ghost function LoopTermination(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      it1HasPeek: bool,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      it2HasPeek: bool,
      b: bool
    ): int
    reads s1, s1.Repr(), s2, s2.Repr(), it1, it2
    requires LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
  {
    |s2.Model()| - it2.Index() + (if b then 1 else 0)
  }

  method Loop1(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      it1HasPeek: bool,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      it2HasPeek: bool,
      b: bool
    )
    returns (
      newIt1HasPeek: bool,
      newIt2HasPeek: bool,
      newB: bool
    )
    modifies s1, s1.Repr(), s2, s2.Repr()
    ensures fresh(s1.Repr() - old(s1.Repr()))
    ensures fresh(s2.Repr() - old(s2.Repr()))
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())
    requires it1HasPeek && it2HasPeek && b
    requires LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
    ensures LoopInvariant(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
    ensures DynamicInvariant(s1, s2)
    ensures LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))

    requires it1.Peek?() == it2.Peek?()
  {
    it1.Next();
    newIt1HasPeek := it1.HasPeek();
    it2.Next();
    newIt2HasPeek := it2.HasPeek();
    newB := b;
  }

  method Loop2(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      it1HasPeek: bool,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      it2HasPeek: bool,
      b: bool
    )
    returns (
      newIt1HasPeek: bool,
      newIt2HasPeek: bool,
      newB: bool
    )
    modifies s1, s1.Repr(), s2, s2.Repr()
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())
    requires it1HasPeek && it2HasPeek && b
    requires LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
    ensures LoopInvariant(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
    ensures DynamicInvariant(s1, s2)
    ensures LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))

    requires it1.Peek?() < it2.Peek?()
  {
    newB := false;
    it1.Next();
    newIt1HasPeek := it1.HasPeek();
    newIt2HasPeek := it2.HasPeek();
  }

  method Loop3(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      it1HasPeek: bool,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      it2HasPeek: bool,
      b: bool
    )
    returns (
      newIt1HasPeek: bool,
      newIt2HasPeek: bool,
      newB: bool
    )
    modifies s1, s1.Repr(), s2, s2.Repr()
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())
    requires it1HasPeek && it2HasPeek && b
    requires LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
    ensures LoopInvariant(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
    ensures DynamicInvariant(s1, s2)
    ensures LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))

    requires it1.Peek?() > it2.Peek?()
  {
    it2.Next();
    newB := b;
    newIt1HasPeek := it1.HasPeek();
    newIt2HasPeek := it2.HasPeek();
  }

  method Loop(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      it1HasPeek: bool,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      it2HasPeek: bool,
      b: bool
    )
    returns (
      newIt1HasPeek: bool,
      newIt2HasPeek: bool,
      newB: bool
    )
    modifies s1, s1.Repr(), s2, s2.Repr()
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())
    requires it1HasPeek && it2HasPeek && b
    requires LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
    ensures LoopInvariant(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
    ensures DynamicInvariant(s1, s2)
    ensures LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))
  {
    var it1Peek := it1.Peek();
    var it2Peek := it2.Peek();
    if it1Peek == it2Peek {
      label PreLoop1:
      newIt1HasPeek, newIt2HasPeek, newB := Loop1(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b);
    } else if it1Peek < it2Peek {
      newIt1HasPeek, newIt2HasPeek, newB := Loop2(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b);
    } else {
      newIt1HasPeek, newIt2HasPeek, newB := Loop3(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b);
    }
  }

  method OrdSetContained(s1: OrderedSet, s2: OrderedSet) returns (b: bool)
    modifies s1, s1.Repr(), s2, s2.Repr()
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())

    //requires StaticInvariant(s1, s2)
    requires s1.Valid() && s2.Valid()
    requires {s1} + s1.Repr() !! {s2} + s2.Repr()

    //ensures StaticInvariant(s1, s2)
    ensures s1.Valid() && s2.Valid()
    ensures {s1} + s1.Repr() !! {s2} + s2.Repr()

    //ensures DynamicInvariant(s1, s2)
    ensures fresh(s1.Repr() - old(s1.Repr()))
    ensures fresh(s2.Repr() - old(s2.Repr()))
    ensures s1.Iterators() >= old(s1.Iterators())
    ensures s2.Iterators() >= old(s2.Iterators())
    ensures s1.Model() == old(s1.Model())
    ensures s2.Model() == old(s2.Model())

    ensures b == (s1.Model() <= s2.Model())
  {
    var it1: OrderedSetIterator := s1.First();
    var it2: OrderedSetIterator := s2.First();
    var it1HasPeek := it1.HasPeek();
    var it2HasPeek := it2.HasPeek();
    b := true;

    while it1HasPeek && it2HasPeek && b
      decreases LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
      invariant allocated(s1.Repr())
      invariant allocated(s2.Repr())
      invariant LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
      invariant DynamicInvariant(s1, s2)
    {
      it1HasPeek, it2HasPeek, b := Loop(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b);
      /*
      var it1Peek := it1.Peek();
      var it2Peek := it2.Peek();
      if it1Peek == it2Peek {
        it1HasPeek, it2HasPeek, b := Loop1(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b);
      } else if it1Peek < it2Peek {
        it1HasPeek, it2HasPeek, b := Loop2(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b);
      } else {
        it1HasPeek, it2HasPeek, b := Loop3(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b);
      }
      */
    }
    b := b && !it1HasPeek;
  }
}
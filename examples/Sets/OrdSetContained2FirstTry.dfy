include "../../src/ADT.dfy"
include "../../src/OrderedSet/OrderedSetSpec2.dfy"

module OrdSetContained {
  import opened OrderedSetSpec2
  import opened ADT

  export provides ADT, OrderedSetSpec2, OrdSetContained

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
    && Invariant2(s1, s2)
    && it1.Parent() == s1
    && it2.Parent() == s2
    && it1.Valid()
    && it2.Valid()
    && it1 in s1.Iterators()
    && it2 in s2.Iterators()
    && it1HasPeek == it1.HasPeek?()
    && it2HasPeek == it2.HasPeek?()

    //&& (b ==> it1.Traversed() <= it2.Traversed())
    //&& (!b ==> !(it1.Traversed() <= s2.Model()))
    //&& (it1.HasPeek?() ==> it1.Peek?() !in it2.Traversed())
    //&& (forall u | u in it2.Traversed() && it1.Traversed() < s1.Model() :: u < it1.Peek?())
  }

  twostate predicate MaintainsLoopInvariant(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      it1HasPeek: bool,
      newIt1HasPeek: bool,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      it2HasPeek: bool,
      newIt2HasPeek: bool,
      b: bool,
      newB: bool
    )
    reads s1, s1.Repr(), s2, s2.Repr(), it1, it2
    requires old(LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))
  {
    && LoopInvariant(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
    && MaintainsInvariant2(s1, s2)
    && s1.Iterators() >= old(s1.Iterators())
    && s2.Iterators() >= old(s2.Iterators())
  }

  ghost function LoopBound(
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
    |s2.Model()| - |it2.Before'()| + (if b then 1 else 0)
  }

  // 15.3M
  method {:only} Loop(
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
    ensures MaintainsLoopInvariant(s1, it1, it1HasPeek, newIt1HasPeek, s2, it2, it2HasPeek, newIt2HasPeek, b, newB)
    //ensures LoopBound(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      //< old(LoopBound(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))
  {
    var it1Peek := it1.Peek();
    var it2Peek := it2.Peek();
    if it1Peek == it2Peek {
      it1.Next();
      newIt1HasPeek := it1.HasPeek();
      it2.Next();
      newIt2HasPeek := it2.HasPeek();
      newB := b;
    } else if it1Peek < it2Peek {
      newB := false;
      it1.Next();
      newIt1HasPeek := it1.HasPeek();
      newIt2HasPeek := it2.HasPeek();
    } else {
      it2.Next();
      newB := b;
      newIt1HasPeek := it1.HasPeek();
      newIt2HasPeek := it2.HasPeek();
    }
  }

  // 6.08M RU
  method OrdSetContained(s1: OrderedSet, s2: OrderedSet) returns (b: bool)
    modifies s1, s1.Repr(), s2, s2.Repr()
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())

    requires Invariant2(s1, s2)
    //requires s1.Valid() && s2.Valid()
    //requires {s1} + s1.Repr() !! {s2} + s2.Repr()

    //ensures Invariant(s1, s2)
    //ensures s1.Valid() && s2.Valid()
    //ensures {s1} + s1.Repr() !! {s2} + s2.Repr()

    //ensures DynamicInvariant(s1, s2)
    ensures MaintainsInvariant2(s1, s2)
    ensures s1.Iterators() >= old(s1.Iterators())
    ensures s2.Iterators() >= old(s2.Iterators())
    //ensures s1.Model() == old(s1.Model())
    //ensures s2.Model() == old(s2.Model())

    //ensures b == (s1.Model() <= s2.Model())
  {
    var it1: OrderedSetIterator := s1.First();
    var it2: OrderedSetIterator := s2.First();
    var it1HasPeek := it1.HasPeek();
    var it2HasPeek := it2.HasPeek();
    b := true;

    while it1HasPeek && it2HasPeek && b
      decreases LoopBound(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
      invariant allocated(s1.Repr())
      invariant allocated(s2.Repr())
      invariant LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
      invariant MaintainsInvariant2(s1, s2)
      invariant s1.Iterators() >= old(s1.Iterators())
      invariant s2.Iterators() >= old(s2.Iterators())
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
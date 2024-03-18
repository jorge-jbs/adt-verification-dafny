include "../../src/ADT.dfy"
include "../../src/OrderedSet/OrderedSetOpaqueSpec.dfy"

module OrdSetContained {
  import opened OrderedSetSpec
  import opened ADT

  export provides OrderedSetSpec, OrdSetContained

  opaque ghost predicate StaticInvariant(s1: OrderedSet, s2: OrderedSet)
    reads s1, s1.Repr(), s2, s2.Repr()
  {
    && s1.Valid() && s2.Valid()
    && {s1} + s1.Repr() !! {s2} + s2.Repr()
  }

  opaque twostate predicate DynamicInvariant(s1: OrderedSet, s2: OrderedSet)
    reads s1, s1.Repr(), s2, s2.Repr()
    requires old(StaticInvariant(s1, s2))
    requires StaticInvariant(s1, s2)
  {
    reveal StaticInvariant();
    && fresh(s1.Repr() - old(s1.Repr()))
    && fresh(s2.Repr() - old(s2.Repr()))
    && s1.Iterators() >= old(s1.Iterators())
    && s2.Iterators() >= old(s2.Iterators())
    && s1.Model() == old(s1.Model())
    && s2.Model() == old(s2.Model())
  }

  opaque ghost predicate LoopInvariant(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      it1HasPeek: bool,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      it2HasPeek: bool,
      b: bool
    )
    reads s1, s1.Repr(), s2, s2.Repr(), it1, it2
    ensures LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
      ==> StaticInvariant(s1, s2)
  {
    && StaticInvariant(s1, s2)

    && it1.Parent() == s1
    && it2.Parent() == s2
    && it1.Valid()
    && it2.Valid()
    && it1 in s1.Iterators()
    && it2 in s2.Iterators()
    //&& it1.Traversed() <= s1.Model()
    //&& it2.Traversed() <= s2.Model()
    //&& 0 <= it1.Index() <= |s1.Model()|
    //&& 0 <= it2.Index() <= |s2.Model()|
    //&& !it2.HasNext()==> b
    && (b ==> it1.Traversed() <= it2.Traversed())
    && (!b ==> !(it1.Traversed() <= s2.Model()))
    && (it1.HasPeek?() ==> it1.Peek?() !in it2.Traversed())
    && (forall u | u in it2.Traversed() && it1.Traversed() < s1.Model() :: u < it1.Peek?())

    && it1HasPeek == it1.HasPeek?()
    && it2HasPeek == it2.HasPeek?()
  }

  opaque ghost function LoopTermination(
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
    |s2.Model()| - |it2.Traversed()| + (if b then 1 else 0)
  }

  twostate predicate Loop1Invariant(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      s2: OrderedSet,
      it2: OrderedSetIterator
    )
    reads s1, s1.Repr(), s2, s2.Repr(), it1, it2
  {
    && StaticInvariant(s1, s2)

    && it1.Parent() == s1
    && it2.Parent() == s2
    && it1.Valid()
    && it2.Valid()
    && it1 in s1.Iterators()
    && it2 in s2.Iterators()
    //&& it1.Traversed() <= it2.Traversed()
    //&& (it1.HasPeek?() ==> it1.Peek?() !in it2.Traversed())
    //&& (forall u | u in it2.Traversed() && it1.Traversed() < s1.Model() :: u < it1.Peek?())
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
    ensures 0 <= LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))

    requires it1.Peek?() == it2.Peek?()
  {
    it1.Next();
    newIt1HasPeek := it1.HasPeek();
    it2.Next();
    newIt2HasPeek := it2.HasPeek();
    newB := b;
  }

/*
  method {:vcs_split_on_every_assert} Loop1(  // 14.2M ==> 13.7M
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
    //requires allocated({s1} + s1.Repr())
    //requires allocated({s2} + s2.Repr())
    //ensures allocated({s1} + s1.Repr())
    //ensures allocated({s1} + s2.Repr())
    requires allocated(s1)
    requires allocated(s1.Repr())
    requires allocated(s2)
    requires allocated(s2.Repr())
    ensures allocated(s1)
    ensures allocated(s1.Repr())
    ensures allocated(s2)
    ensures allocated(s2.Repr())
    requires it1HasPeek && it2HasPeek && b
    requires LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
    //ensures StaticInvariant(s1, s2)
    requires LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
    ensures LoopInvariant(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
    ensures DynamicInvariant(s1, s2)
    ensures LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))

    requires it1.Peek?() == it2.Peek?()
  {
    it1.Next();
    assert Loop1Invariant(s1, it1, s2, it2);
    newIt1HasPeek := it1.HasPeek();
    assert Loop1Invariant(s1, it1, s2, it2);
    it2.Next();
    assert Loop1Invariant(s1, it1, s2, it2);
    newIt2HasPeek := it2.HasPeek();
    assert Loop1Invariant(s1, it1, s2, it2);
    newB := b;
  }
  */
    /*
  {
    ghost var repr1 := {s1} + s1.Repr();
    ghost var repr2 := {s2} + s2.Repr();
    ////assert allocated(repr2);
    it1.Next();
    ghost var repr1' := {s1} + s1.Repr();
    //assert s1 in repr1;
    //assert s1 in repr1';
    //assert fresh(repr1' - repr1);
    ghost var repr2' := {s2} + s2.Repr();
    //assert repr2 == repr2';
    Disjoint(repr1', repr1, repr2');
    //assert StaticInvariant(s1, s2);
    assert {:split_here} Loop1Invariant(s1, it1, s2, it2);
    //assert {:split_here} StaticInvariant(s1, s2);
  label L2:
    newIt1HasPeek := it1.HasPeek();
    ghost var repr1'' := {s1} + s1.Repr();
    ghost var repr2'' := {s2} + s2.Repr();
    Disjoint@L2(repr1'', repr1', repr2'');
    assert {:split_here} Loop1Invariant(s1, it1, s2, it2);
    //assert {:split_here} StaticInvariant(s1, s2);
  label L3:
    it2.Next();
    ghost var repr1''' := {s1} + s1.Repr();
    ghost var repr2''' := {s2} + s2.Repr();
    Disjoint@L3(repr2''', repr2'', repr1''');
    assert {:split_here} Loop1Invariant(s1, it1, s2, it2);
    //assert {:split_here} StaticInvariant(s1, s2);
  label L4:
    newIt2HasPeek := it2.HasPeek();
    ghost var repr1'''' := {s1} + s1.Repr();
    ghost var repr2'''' := {s2} + s2.Repr();
    Disjoint@L4(repr2'''', repr2''', repr1'''');
    assert {:split_here} Loop1Invariant(s1, it1, s2, it2);
    //assert {:split_here} StaticInvariant(s1, s2);
    newB := b;
  }
  */

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
    ensures 0 <= LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))

    requires it1.Peek?() < it2.Peek?()
  {
    newB := false;
    it1.Next();
    newIt1HasPeek := it1.HasPeek();
    newIt2HasPeek := it2.HasPeek();
  }

  method {:only} Loop3(
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
    ensures 0 <= LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))

    requires
      assert it1.Valid() && it2.Valid() && it1.HasPeek?() && it2.HasPeek?() by { reveal StaticInvariant(), LoopInvariant(); }
      it1.Peek?() > it2.Peek?()
  {
    assert 
      && s1.Valid() && s2.Valid()
      && {s1} + s1.Repr() !! {s2} + s2.Repr()
      && it1.Parent() == s1
      && it2.Parent() == s2
      && it1.Valid()
      && it2.Valid()
      && it1 in s1.Iterators()
      && it2 in s2.Iterators()
      && it1HasPeek == it1.HasPeek?()
      && it2HasPeek == it2.HasPeek?()
    by {
      reveal StaticInvariant(), LoopInvariant();
    }
    it2.Next();
    newB := b;
    newIt1HasPeek := it1.HasPeek();
    newIt2HasPeek := it2.HasPeek();
    assert {:only}
      && LoopInvariant(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      && DynamicInvariant(s1, s2)
    by {
      reveal it2.NextModel(), it1.HasPeekModel(), StaticInvariant(), DynamicInvariant(), LoopInvariant();
    }
    assert 0 <= LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
        < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))
    by {
      reveal LoopTermination(), StaticInvariant(), DynamicInvariant(), LoopInvariant();
    }
  }

  // 7.72M RU ==> 3.85M RU
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
    ensures LoopInvariant(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
    ensures DynamicInvariant(s1, s2)
    ensures 0 <= LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))
  {
    assert 
      && s1.Valid() && s2.Valid()
      && {s1} + s1.Repr() !! {s2} + s2.Repr()
      && it1.Parent() == s1
      && it2.Parent() == s2
      && it1.Valid()
      && it2.Valid()
      && it1 in s1.Iterators()
      && it2 in s2.Iterators()
      && it1HasPeek == it1.HasPeek?()
      && it2HasPeek == it2.HasPeek?()
    by {
      reveal StaticInvariant(), LoopInvariant();
    }
    var it1Peek := it1.Peek();
    var it2Peek := it2.Peek();
    assert
      && LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
      && DynamicInvariant(s1, s2)
      && it1Peek == it1.Peek?()
      && it2Peek == it2.Peek?()
    by {
      reveal it1.PeekModel(), it2.PeekModel(), StaticInvariant(), DynamicInvariant(), LoopInvariant();
    }
    assert
      LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
      == old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))
    by {
      reveal it1.PeekModel(), LoopTermination();
    }
  label PreIf:
    if it1Peek == it2Peek {
      newIt1HasPeek, newIt2HasPeek, newB := Loop1(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b);
    } else if it1Peek < it2Peek {
      newIt1HasPeek, newIt2HasPeek, newB := Loop2(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b);
    } else {
      newIt1HasPeek, newIt2HasPeek, newB := Loop3(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b);
    }
    assert LoopInvariant(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB);
    assert DynamicInvariant(s1, s2) by {
      reveal StaticInvariant(), DynamicInvariant(), LoopInvariant();
    }
    assert
      0
      <= LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))
    by {
      reveal LoopTermination(), StaticInvariant(), DynamicInvariant(), LoopInvariant();
    }
  }

  // 6.85M RU ==> 3.53M RU
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
    assert StaticInvariant(s1, s2) by {
      reveal StaticInvariant();
    }
    var it1: OrderedSetIterator := s1.First();
    var it2: OrderedSetIterator := s2.First();
    var it1HasPeek := it1.HasPeek();
    var it2HasPeek := it2.HasPeek();
    b := true;

    assert
      && LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
      && DynamicInvariant(s1, s2)
    by {
      assume false;
    }

    while it1HasPeek && it2HasPeek && b
      decreases LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
      invariant allocated(s1.Repr())
      invariant allocated(s2.Repr())
      invariant LoopInvariant(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
      invariant DynamicInvariant(s1, s2)
    {
      assert
        && fresh(s1.Repr() - old(s1.Repr()))
        && fresh(s2.Repr() - old(s2.Repr()))
      by {
        reveal DynamicInvariant();
      }
      it1HasPeek, it2HasPeek, b := Loop(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b);
      assert DynamicInvariant(s1, s2) by {
        reveal DynamicInvariant();
      }
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

    assert
      && s1.Valid() && s2.Valid()
      && {s1} + s1.Repr() !! {s2} + s2.Repr()
    by {
      reveal StaticInvariant();
    }

    assert
      && fresh(s1.Repr() - old(s1.Repr()))
      && fresh(s2.Repr() - old(s2.Repr()))
      && s1.Iterators() >= old(s1.Iterators())
      && s2.Iterators() >= old(s2.Iterators())
      && s1.Model() == old(s1.Model())
      && s2.Model() == old(s2.Model())
    by {
      reveal DynamicInvariant();
    }

    assert b == (s1.Model() <= s2.Model()) by {
      reveal LoopInvariant();
    }
  }
}
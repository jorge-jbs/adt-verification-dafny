include "../../src/UnorderedSet/UnorderedSetSpec.dfy"

module ContainedNoModel {
  import opened UnorderedSetSpec
  import opened ADT

  ghost predicate ValidIt(s: UnorderedSet, it: UnorderedSetIterator)
    reads s.Repr()
    requires s.Valid()
  {
    && it.Parent() == s
    && it in s.Iterators()
    && it.Valid()
  }

  ghost predicate Valid2It10(
      a: UnorderedSet,
      itA: UnorderedSetIterator,
      b: UnorderedSet
    )
    reads a.Repr(), b.Repr()
  {
    && Valid2(a, b)
    && ValidIt(a, itA)
  }

  opaque ghost function LoopBound(
      s1: UnorderedSet, 
      it1: UnorderedSetIterator, 
      s2: UnorderedSet,
      b: bool
    ): nat
    reads s1.Repr(), s2.Repr()
    requires Valid2It10(s1, it1, s2)
  {
    reveal UnorderedSetIterator.TraversedSpec();
    |s1.Model()| - |it1.Traversed()| + (if b then 1 else 0)
  }

  method Contained(s1: UnorderedSet, s2: UnorderedSet) returns (b: bool)
    modifies s1.Repr(), s2.Repr()
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())
    ensures fresh(s1.Repr()-old(s1.Repr()))
    ensures fresh(s2.Repr()-old(s2.Repr()))

    requires Valid2(s1, s2)
    ensures Valid2(s1, s2)

    ensures s1.Iterators() >= old(s1.Iterators())
    ensures s2.Iterators() >= old(s2.Iterators())
  {
    var it1 := s1.First();
    assert Valid2It10(s1, it1, s2);

    b := true;
    var it1HasPeek := it1.HasPeek();

    while it1HasPeek && b
      decreases LoopBound(s1, it1, s2, b)
      invariant allocated(s1.Repr())
      invariant allocated(s2.Repr())
      invariant fresh(s1.Repr()-old(s1.Repr()))
      invariant fresh(s2.Repr()-old(s2.Repr()))

      invariant Valid2It10(s1, it1, s2)
      invariant it1HasPeek == it1.HasPeek?()

      invariant s1.Iterators() >= old(s1.Iterators())
      invariant s2.Iterators() >= old(s2.Iterators())
    {
      ghost var  initialLoopBound := LoopBound(s1, it1, s2, b);
      var p := it1.Peek();
      b := s2.Contains(p);
      it1.Next();
      it1HasPeek := it1.HasPeek();
      assert LoopBound(s1, it1, s2, b) < initialLoopBound by {
        reveal LoopBound();
        reveal it1.PeekModel(), s2.ContainsModel(), it1.NextModel(), it1.HasPeekModel();
      }
    }
  }
}
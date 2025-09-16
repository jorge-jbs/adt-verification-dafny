include "../../src/OrderedSet/OrderedSetSpec.dfy"

module IntersectionNoModel {
  import opened KeyValue
  import opened ADT
  import opened OrderedSetSpec

  export provides OrderedSetSpec, ADT, OrdSetIntersection

  opaque ghost function LoopBound(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      su: OrderedSet
    ): nat
    reads s1.Repr(), s2.Repr(), su.Repr()
    requires Valid3It110(s1, it1, s2, it2, su)
  {
    reveal OrderedSetIterator.TraversedSpec();
    (|s1.Model()| - |it1.Traversed()|) + (|s2.Model()| - |it2.Traversed()|)
  }

  // 11.7M RU - correctness verification and termination (with helper)
  // 15.0M RU - correctness verification and termination (without helper)
  method Loop(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      su: OrderedSet
    )
    returns (
      it1HasPeek: bool,
      it2HasPeek: bool
    )
    modifies s1.Repr(), s2.Repr(), su.Repr()
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    requires allocated(su.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())
    ensures allocated(su.Repr())
    ensures fresh(s1.Repr()-old(s1.Repr()))
    ensures fresh(s2.Repr()-old(s2.Repr()))
    ensures fresh(su.Repr()-old(su.Repr()))

    requires Valid3It110(s1, it1, s2, it2, su)
    requires it1.HasPeek?()
    requires it2.HasPeek?()
    ensures Valid3It110(s1, it1, s2, it2, su)
    ensures it1HasPeek == it1.HasPeek?()
    ensures it2HasPeek == it2.HasPeek?()
    ensures LoopBound(s1, it1, s2, it2, su) < old(LoopBound(s1, it1, s2, it2, su))

    ensures s1.Iterators() >= old(s1.Iterators())
    ensures s2.Iterators() >= old(s2.Iterators())
    ensures su.Iterators() >= old(su.Iterators())
  {
    var it1Peek := it1.Peek();
    //MaintainsValid3It110Helper(s1, it1, s2, it2, su);
    assert Valid3It110(s1, it1, s2, it2, su);
    //label L1:
    var it2Peek := it2.Peek();
    //MaintainsValid3It110Helper@L1(s2, it2, s1, it1, su);
    assert Valid3It110(s1, it1, s2, it2, su);
    if it1Peek == it2Peek {
      //label L2:
      su.Add(it1Peek);
      //MaintainsValid3Helper@L2(su, s2, s1);
      assert Valid3It110(s1, it1, s2, it2, su);
      //label L3:
      it1.Next();
      //MaintainsValid3It110Helper@L3(s1, it1, s2, it2, su);
      assert Valid3It110(s1, it1, s2, it2, su);
      //label L4:
      it2.Next();
      //MaintainsValid3It110Helper@L4(s2, it2, s1, it1, su);
      assert Valid3It110(s1, it1, s2, it2, su);
    } else if it1Peek < it2Peek {
      //label L5:
      it1.Next();
      //MaintainsValid3It110Helper@L5(s1, it1, s2, it2, su);
      assert Valid3It110(s1, it1, s2, it2, su);
    } else {
      //label L6:
      it2.Next();
      //MaintainsValid3It110Helper@L6(s2, it2, s1, it1, su);
      assert Valid3It110(s1, it1, s2, it2, su);
    }
    assert Valid3It110(s1, it1, s2, it2, su);
    //label L7:
    it1HasPeek := it1.HasPeek();
    //MaintainsValid3It110Helper@L7(s1, it1, s2, it2, su);
    assert Valid3It110(s1, it1, s2, it2, su);
    //label L8:
    it2HasPeek := it2.HasPeek();
    //MaintainsValid3It110Helper@L8(s2, it2, s1, it1, su);
    assert Valid3It110(s1, it1, s2, it2, su);
    assert LoopBound(s1, it1, s2, it2, su) < old(LoopBound(s1, it1, s2, it2, su)) by {
      reveal LoopBound();
      reveal OrderedSetIterator.PeekModel();
      reveal OrderedSet.AddModel();
      reveal OrderedSetIterator.NextModel();
      reveal OrderedSetIterator.HasPeekModel();
    }
  }

  // 5.75M RU
  method OrdSetIntersection(s1: OrderedSet, s2: OrderedSet, su: OrderedSet)
    modifies s1.Repr(), s2.Repr(), su.Repr()
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    requires allocated(su.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())
    ensures allocated(su.Repr())
    ensures fresh(s1.Repr()-old(s1.Repr()))
    ensures fresh(s2.Repr()-old(s2.Repr()))
    ensures fresh(su.Repr()-old(su.Repr()))

    requires Valid3(s1, s2, su)

    ensures Valid3(s1, s2, su)

    ensures s1.Iterators() >= old(s1.Iterators())
    ensures s2.Iterators() >= old(s2.Iterators())
    ensures su.Iterators() >= old(su.Iterators())
  {
    var it1: OrderedSetIterator := s1.First();
    var it2: OrderedSetIterator := s2.First();
    assert Valid3It110(s1, it1, s2, it2, su);
    var it1HasPeek := it1.HasPeek();
    assert Valid3It110(s1, it1, s2, it2, su);
    var it2HasPeek := it2.HasPeek();
    assert Valid3It110(s1, it1, s2, it2, su);
    while it1HasPeek && it2HasPeek
      decreases LoopBound(s1, it1, s2, it2, su)
      invariant Valid3It110(s1, it1, s2, it2, su)
      invariant it1HasPeek == it1.HasPeek?()
      invariant it2HasPeek == it2.HasPeek?()

      invariant allocated(s1.Repr())
      invariant allocated(s2.Repr())
      invariant allocated(su.Repr())
      invariant fresh(s1.Repr()-old(s1.Repr()))
      invariant fresh(s2.Repr()-old(s2.Repr()))
      invariant fresh(su.Repr()-old(su.Repr()))
      invariant s1.Iterators() >= old(s1.Iterators())
      invariant s2.Iterators() >= old(s2.Iterators())
      invariant su.Iterators() >= old(su.Iterators())
    {
      it1HasPeek, it2HasPeek := Loop(s1, it1, s2, it2, su);
      assert Valid3It110(s1, it1, s2, it2, su);
    }
  }
}
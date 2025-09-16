include "../../src/OrderedSet/OrderedSetSpec.dfy"

module Intersection {
  import opened KeyValue
  import opened ADT
  import opened OrderedSetSpec

  export provides OrderedSetSpec, ADT, OrdSetIntersection, OrdSetIntersectionModel, OrdSetIntersectionModelPre

  opaque ghost predicate LoopInvariant(
      s1: OrderedSet,
      s1Model: set<K>,
      it1: OrderedSetIterator,
      s2: OrderedSet,
      s2Model: set<K>,
      it2: OrderedSetIterator,
      su: OrderedSet
    )
    reads s1.Repr(), s2.Repr(), su.Repr()
    requires Valid3It110(s1, it1, s2, it2, su)
  {
    && s1.Model() == s1Model
    && s2.Model() == s2Model
    && su.Model() == it1.Traversed() * it2.Traversed()
    && (forall a <- it1.Traversed(), b <- s2.Model()-it2.Traversed() :: a < b)
    && (forall a <- it2.Traversed(), b <- s1.Model()-it1.Traversed() :: a < b)
  }

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

  // 13.9M RU - correctness and termination
  // 39.6M RU - everything
  method LoopBody(
      s1: OrderedSet,
      ghost s1Model: set<K>,
      it1: OrderedSetIterator,
      s2: OrderedSet,
      ghost s2Model: set<K>,
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
    ensures Fresh3(s1, s2, su)

    requires Valid3It110(s1, it1, s2, it2, su)
    requires it1.HasPeek?()
    requires it2.HasPeek?()
    requires LoopInvariant(s1, s1Model, it1, s2, s2Model, it2, su)

    ensures Valid3It110(s1, it1, s2, it2, su)
    ensures it1HasPeek == it1.HasPeek?()
    ensures it2HasPeek == it2.HasPeek?()
    ensures LoopBound(s1, it1, s2, it2, su) < old(LoopBound(s1, it1, s2, it2, su))
    ensures LoopInvariant(s1, s1Model, it1, s2, s2Model, it2, su)

    ensures s1.Iterators() >= old(s1.Iterators())
    ensures s2.Iterators() >= old(s2.Iterators())
    ensures su.Iterators() >= old(su.Iterators())
  {
    var it1Peek := it1.Peek();
    assert Valid3It110(s1, it1, s2, it2, su);

    var it2Peek := it2.Peek();
    assert Valid3It110(s1, it1, s2, it2, su);

    if it1Peek == it2Peek {
      su.Add(it1Peek);
      assert Valid3It110(s1, it1, s2, it2, su);

      it1.Next();
      assert Valid3It110(s1, it1, s2, it2, su);

      it2.Next();
      assert Valid3It110(s1, it1, s2, it2, su);

      assert LoopInvariant(s1, s1Model, it1, s2, s2Model, it2, su) by {
        reveal LoopInvariant();
        reveal OrderedSetIterator.PeekModel();
        reveal OrderedSetIterator.PeekSpec();
        reveal OrderedSetIterator.PeekOrderSpec();
        reveal OrderedSet.AddModel();
        reveal OrderedSetIterator.NextModel();
      }
    } else if it1Peek < it2Peek {
      assert pre:
        && (forall y | y in s2.Model()-it2.Traversed():: it1.Peek?()<it2.Peek?()<=y)
        && it1.Peek?() < it2.Peek?()
        && it1Peek in s1.Model()-it1.Traversed()
        && (forall x | x in it2.Traversed() :: x < it1Peek)
        && it1Peek !in it2.Traversed()
      by {
        reveal LoopInvariant();
        reveal OrderedSetIterator.PeekModel();
        reveal OrderedSetIterator.PeekSpec();
        reveal OrderedSetIterator.PeekOrderSpec();
        reveal OrderedSetIterator.NextModel();
      }

      it1.Next();
      assert Valid3It110(s1, it1, s2, it2, su);

      assert LoopInvariant(s1, s1Model, it1, s2, s2Model, it2, su) by {
        reveal LoopInvariant(), pre;
        reveal OrderedSetIterator.PeekModel();
        reveal OrderedSetIterator.PeekSpec();
        reveal OrderedSetIterator.PeekOrderSpec();
        reveal OrderedSetIterator.NextModel();
        assert forall x, y |  x in it1.Traversed() && y in s2.Model()-it2.Traversed():: x < y;
        assert forall x, y |  x in it2.Traversed() && y in s1.Model()-it1.Traversed():: x < y;

        calc == {
          it1.Traversed() * it2.Traversed();
          {assert it1.Traversed() == old(it1.Traversed())+{it1Peek};
           assert  it2.Traversed() == old(it2.Traversed());}
          (old(it1.Traversed())+{it1Peek}) * it2.Traversed();
          (old(it1.Traversed())*old(it2.Traversed()))+({it1Peek}*old(it2.Traversed()));
          {assert it1Peek !in old(it2.Traversed());}
          old(it1.Traversed()) * old(it2.Traversed());
          su.Model();
        }
      }
    } else {
      assert pre:
        && (forall y | y in s1.Model()-it1.Traversed():: it2.Peek?()<it1.Peek?()<=y)
        && it1.Peek?() > it2.Peek?()
        && it2Peek in s2.Model()-it2.Traversed()
        && (forall x | x in it1.Traversed() :: x < it2Peek)
        && it2Peek !in it1.Traversed()
      by {
        reveal LoopInvariant();
        reveal OrderedSetIterator.PeekModel();
        reveal OrderedSetIterator.PeekSpec();
        reveal OrderedSetIterator.PeekOrderSpec();
        reveal OrderedSetIterator.NextModel();
      }

      it2.Next();
      assert Valid3It110(s1, it1, s2, it2, su);

      assert LoopInvariant(s1, s1Model, it1, s2, s2Model, it2, su) by {
        reveal LoopInvariant(), pre;
        reveal OrderedSetIterator.PeekModel();
        reveal OrderedSetIterator.PeekSpec();
        reveal OrderedSetIterator.PeekOrderSpec();
        reveal OrderedSetIterator.NextModel();

        assert forall x, y |  x in it1.Traversed() && y in s2.Model()-it2.Traversed():: x < y;
        assert forall x, y |  x in it2.Traversed() && y in s1.Model()-it1.Traversed():: x < y;

        calc == {
          it1.Traversed() * it2.Traversed();
          {assert it2.Traversed() == old(it2.Traversed())+{it2Peek};
           assert  it1.Traversed() == old(it1.Traversed());}
          (old(it1.Traversed())) * (old(it2.Traversed())+{it2Peek});
          (old(it1.Traversed())*old(it2.Traversed()))+(old(it1.Traversed())*{it2Peek});
          {assert it2Peek !in old(it1.Traversed());}
          old(it1.Traversed()) * old(it2.Traversed());
          su.Model();
        }
      }
    }
    assert LoopInvariant(s1, s1Model, it1, s2, s2Model, it2, su);
    assert Valid3It110(s1, it1, s2, it2, su);

    it1HasPeek := it1.HasPeek();
    assert Valid3It110(s1, it1, s2, it2, su);

    it2HasPeek := it2.HasPeek();
    assert Valid3It110(s1, it1, s2, it2, su);

    assert LoopBound(s1, it1, s2, it2, su) < old(LoopBound(s1, it1, s2, it2, su)) by {
      reveal LoopBound();
      reveal OrderedSetIterator.PeekModel();
      reveal OrderedSet.AddModel();
      reveal OrderedSetIterator.NextModel();
      reveal OrderedSetIterator.HasPeekModel();
    }

    assert LoopInvariant(s1, s1Model, it1, s2, s2Model, it2, su) by {
      reveal LoopInvariant();
      reveal OrderedSetIterator.HasPeekModel();
    }
  }

  opaque ghost predicate OrdSetIntersectionModelPre(
      s1: OrderedSet,
      s2: OrderedSet,
      su: OrderedSet
    )
    reads s1.Repr(), s2.Repr(), su.Repr()
    requires Valid3(s1, s2, su)
  {
    su.Model() == {}
  }

  opaque twostate predicate OrdSetIntersectionModel(
      s1: OrderedSet,
      s2: OrderedSet,
      su: OrderedSet
    )
    reads s1.Repr(), s2.Repr(), su.Repr()
    requires old(Valid3(s1, s2, su))
    requires Valid3(s1, s2, su)
  {
    && s1.Model() == old(s1.Model())
    && s2.Model() == old(s2.Model())
    && su.Model() == s1.Model() * s2.Model()
  }

  twostate lemma LoopInvariantImpliesOrdSetIntersectionModel(
      s1: OrderedSet,
      new it1: OrderedSetIterator,
      s2: OrderedSet,
      new it2: OrderedSetIterator,
      su: OrderedSet
    )
    requires old(Valid3(s1, s2, su))
    requires Valid3It110(s1, it1, s2, it2, su)
    requires !it1.HasPeek?() || !it2.HasPeek?()
    requires LoopInvariant(s1, old(s1.Model()), it1, s2, old(s2.Model()), it2, su)
    ensures OrdSetIntersectionModel(s1, s2, su)
  {
    reveal LoopInvariant(), OrdSetIntersectionModel();
    reveal OrderedSetIterator.PeekSpec();
    reveal OrderedSetIterator.BeforeSpec();
    reveal OrderedSetIterator.TraversedSpec();

    assert it1.Traversed() == s1.Model() || it2.Traversed() == s2.Model();
    if it1.Traversed() == s1.Model() {
      calc == {
        su.Model();
        it1.Traversed() * it2.Traversed();
        s1.Model() * it2.Traversed();
        {
          assert (forall a <- it1.Traversed(), b <- s2.Model()-it2.Traversed() :: a < b);
          assert (forall a <- it1.Traversed(), b <- s2.Model()-it2.Traversed() :: a != b);
          assert s2.Model()-it2.Traversed() !! it1.Traversed();
          assert s2.Model()-it2.Traversed() !! s1.Model();
        }
        s1.Model() * s2.Model();
      }
    } else {
      calc == {
        su.Model();
        it1.Traversed() * it2.Traversed();
        it1.Traversed() * s2.Model();
        {
          assert (forall a <- it2.Traversed(), b <- s1.Model()-it1.Traversed() :: a < b);
          assert (forall a <- it2.Traversed(), b <- s1.Model()-it1.Traversed() :: a != b);
          assert s1.Model()-it1.Traversed() !! it2.Traversed();
          assert s1.Model()-it1.Traversed() !! s2.Model();
        }
        s1.Model() * s2.Model();
      }
    }
  }

  // 8.26M RU - with `assert Valid...`
  // 8.16M RU - without `assert Valid...`
  method OrdSetIntersection(s1: OrderedSet, s2: OrderedSet, su: OrderedSet)
    modifies s1.Repr(), s2.Repr(), su.Repr()
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    requires allocated(su.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())
    ensures allocated(su.Repr())
    ensures Fresh3(s1, s2, su)

    requires Valid3(s1, s2, su)
    requires OrdSetIntersectionModelPre(s1, s2, su)

    ensures Valid3(s1, s2, su)
    ensures OrdSetIntersectionModel(s1, s2, su)

    ensures s1.Iterators() >= old(s1.Iterators())
    ensures s2.Iterators() >= old(s2.Iterators())
    ensures su.Iterators() >= old(su.Iterators())
  {
    var it1: OrderedSetIterator := s1.First();
    var it2: OrderedSetIterator := s2.First();
    //assert Valid3It110(s1, it1, s2, it2, su);

    var it1HasPeek := it1.HasPeek();
    //assert Valid3It110(s1, it1, s2, it2, su);

    var it2HasPeek := it2.HasPeek();
    //assert Valid3It110(s1, it1, s2, it2, su);

    assert LoopInvariant(s1, old(s1.Model()), it1, s2, old(s2.Model()), it2, su) by {
      reveal LoopInvariant();
      reveal OrderedSet.FirstModel();
      reveal OrderedSetIterator.HasPeekModel();
      reveal OrdSetIntersectionModelPre();
    }

    while it1HasPeek && it2HasPeek
      decreases LoopBound(s1, it1, s2, it2, su)
      invariant Valid3It110(s1, it1, s2, it2, su)
      invariant it1HasPeek == it1.HasPeek?()
      invariant it2HasPeek == it2.HasPeek?()
      invariant LoopInvariant(s1, old(s1.Model()), it1, s2, old(s2.Model()), it2, su)

      invariant allocated(s1.Repr())
      invariant allocated(s2.Repr())
      invariant allocated(su.Repr())
      invariant Fresh3(s1, s2, su)
      invariant s1.Iterators() >= old(s1.Iterators())
      invariant s2.Iterators() >= old(s2.Iterators())
      invariant su.Iterators() >= old(su.Iterators())
    {
      it1HasPeek, it2HasPeek := LoopBody(s1, old(s1.Model()), it1, s2, old(s2.Model()), it2, su);
      //assert Valid3It110(s1, it1, s2, it2, su);
    }

    LoopInvariantImpliesOrdSetIntersectionModel(s1, it1, s2, it2, su);
  }
}
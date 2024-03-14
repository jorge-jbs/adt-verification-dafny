include "../../src/OrderedSet/OrderedSetSpec2.dfy"

module OrdSetIntersection2 {
  import opened KeyValue
  import opened ADT
  import opened OrderedSetSpec2
  
  //export provides OrderedSetSpec, OrdSetIntersection

  opaque twostate predicate Loop'Model(
      s1: OrderedSet, 
      it1: OrderedSetIterator, 
      s2: OrderedSet, 
      it2: OrderedSetIterator, 
      su: OrderedSet
    )
    reads s1.Repr(), s2.Repr(), su.Repr()
    requires old(Valid3It110(s1, it1, s2, it2, su))
    requires old(it1.HasPeek?())
    requires old(it2.HasPeek?())
    requires Valid3It110(s1, it1, s2, it2, su)
  {
    var x := old(it1.Peek?());
    var y := old(it2.Peek?());
    && s1.Model() == old(s1.Model())
    && s2.Model() == old(s2.Model())
    && (
      if x == y then
        && su.Model() == old(su.Model()) + {x}
        && it1.Traversed() == old(it1.Before()) + {x}
        && it2.Traversed() == old(it2.Before()) + {y}
      else if x < y then
        && su.Model() == old(su.Model())
        && it1.Traversed() == old(it1.Before()) + {x}
        && it2.Traversed() == old(it2.Before())
      else
        && su.Model() == old(su.Model())
        && it1.Traversed() == old(it1.Before())
        && it2.Traversed() == old(it2.Before()) + {y}
    )
  }

  // 6.91M RU - correctness verification  // OUTDATED
  // 6.73M RU - correctness verification (with MaintainsValid...)
  // 2.50M RU - correctness verification (with MaintainsValid..., without it*HasPeek)  // OUTDATED
  // 37.1M RU - correctness and functional verification (with MaintainsValid...)
  // 97.1M RU - correctness and functional verification (without MaintainsValid...)
  method Loop'(
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
    ensures Loop'Model(s1, it1, s2, it2, su)

    ensures s1.Iterators() >= old(s1.Iterators())
    ensures s2.Iterators() >= old(s2.Iterators())
    ensures su.Iterators() >= old(su.Iterators())
  {
    var it1Peek := it1.Peek();
    MaintainsValid3It110Helper(s1, it1, s2, it2, su);
    assert Valid3It110(s1, it1, s2, it2, su);
    label L1:
    var it2Peek := it2.Peek();
    MaintainsValid3It110Helper@L1(s2, it2, s1, it1, su);
    assert Valid3It110(s1, it1, s2, it2, su);
    if it1Peek == it2Peek {
      label L2:
      su.Add(it1Peek); 
      MaintainsValid3Helper@L2(su, s2, s1);
      assert Valid3It110(s1, it1, s2, it2, su);
      label L3:
      it1.Next();
      MaintainsValid3It110Helper@L3(s1, it1, s2, it2, su);
      assert Valid3It110(s1, it1, s2, it2, su);
      label L4:
      it2.Next();
      MaintainsValid3It110Helper@L4(s2, it2, s1, it1, su);
      assert Valid3It110(s1, it1, s2, it2, su);
    } else if it1Peek < it2Peek {
      label L5:
      it1.Next();
      MaintainsValid3It110Helper@L5(s1, it1, s2, it2, su);
      assert Valid3It110(s1, it1, s2, it2, su);
    } else {
      label L6:
      it2.Next();
      MaintainsValid3It110Helper@L6(s2, it2, s1, it1, su);
      assert Valid3It110(s1, it1, s2, it2, su);
    }
    assert Valid3It110(s1, it1, s2, it2, su);
    label L7:
    it1HasPeek := it1.HasPeek();
    MaintainsValid3It110Helper@L7(s1, it1, s2, it2, su);
    assert Valid3It110(s1, it1, s2, it2, su);
    label L8:
    it2HasPeek := it2.HasPeek();
    MaintainsValid3It110Helper@L8(s2, it2, s1, it1, su);
    assert Valid3It110(s1, it1, s2, it2, su);
    assert Loop'Model(s1, it1, s2, it2, su) by {
      reveal Loop'Model();
      reveal OrderedSetIterator.PeekModel();
      reveal OrderedSet.AddModel();
      reveal OrderedSetIterator.NextModel();
      reveal OrderedSetIterator.HasPeekModel();
    }
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

  twostate lemma LoopBoundDecreases(
      s1: OrderedSet, 
      it1: OrderedSetIterator, 
      s2: OrderedSet, 
      it2: OrderedSetIterator, 
      su: OrderedSet
    )
    requires old(Valid3It110(s1, it1, s2, it2, su))
    requires old(it1.HasPeek?())
    requires old(it2.HasPeek?())
    requires Valid3It110(s1, it1, s2, it2, su)
    requires Loop'Model(s1, it1, s2, it2, su)
    ensures LoopBound(s1, it1, s2, it2, su) < old(LoopBound(s1, it1, s2, it2, su))
  {
    reveal Loop'Model(), LoopBound();
    reveal OrderedSetIterator.PeekSpec();
    reveal OrderedSetIterator.TraversedSpec();
  }

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
    && (forall a <- it1.Traversed(), b <- s2.Model() | b !in it2.Traversed() :: a < b)
    && (forall a <- it2.Traversed(), b <- s1.Model() | b !in it1.Traversed() :: a < b)
  }

  twostate lemma LoopMaintainsInvariant(
      s1: OrderedSet, 
      s1Model: set<K>, 
      it1: OrderedSetIterator, 
      s2: OrderedSet, 
      s2Model: set<K>, 
      it2: OrderedSetIterator, 
      su: OrderedSet
    )
    requires old(Valid3It110(s1, it1, s2, it2, su))
    requires old(it1.HasPeek?())
    requires old(it2.HasPeek?())
    requires old(LoopInvariant(s1, s1Model, it1, s2, s2Model, it2, su))
    requires Valid3It110(s1, it1, s2, it2, su)
    requires Loop'Model(s1, it1, s2, it2, su)
    ensures LoopInvariant(s1, s1Model, it1, s2, s2Model, it2, su)
  {
    reveal Loop'Model(), LoopInvariant();
    reveal OrderedSetIterator.PeekSpec();
    reveal OrderedSetIterator.PeekOrderSpec();
    reveal OrderedSetIterator.BeforeSpec();
    reveal OrderedSetIterator.TraversedSpec();
  }

  method Loop(
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
    ensures fresh(s1.Repr()-old(s1.Repr()))
    ensures fresh(s2.Repr()-old(s2.Repr()))
    ensures fresh(su.Repr()-old(su.Repr()))
    

    requires Valid3It110(s1, it1, s2, it2, su)
    requires it1.HasPeek?()
    requires it2.HasPeek?()
    requires LoopInvariant(s1, s1Model, it1, s2, s2Model, it2, su)
    ensures Valid3It110(s1, it1, s2, it2, su)
    ensures it1HasPeek == it1.HasPeek?()
    ensures it2HasPeek == it2.HasPeek?()
    ensures LoopInvariant(s1, s1Model, it1, s2, s2Model, it2, su)
    ensures LoopBound(s1, it1, s2, it2, su) < old(LoopBound(s1, it1, s2, it2, su))

    ensures s1.Iterators() >= old(s1.Iterators())
    ensures s2.Iterators() >= old(s2.Iterators())
    ensures su.Iterators() >= old(su.Iterators())
  {
    it1HasPeek, it2HasPeek := Loop'(s1, it1, s2, it2, su);
    LoopBoundDecreases(s1, it1, s2, it2, su);
    LoopMaintainsInvariant(s1, s1Model, it1, s2, s2Model, it2, su);
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
    assert s1.Model() == old(s1.Model());
    assert s2.Model() == old(s2.Model());
    if !it1.HasPeek?() {
      assert it1.Traversed() == s1.Model();
    }
    if !it2.HasPeek?() {
      assert it2.Traversed() == s2.Model();
    }

    if !it1.HasPeek?() && !it2.HasPeek?() {
      assert su.Model() == s1.Model() * s2.Model();
    } else if it1.HasPeek?() {
      assert su.Model() == it1.Traversed() * s2.Model();
      assert s1.Model() - it1.Traversed() !! s2.Model() by {
        assert (forall a <- it2.Traversed(), b <- s1.Model() | b !in it1.Traversed() :: a < b);
        forall x <- s1.Model() - it1.Traversed()
          ensures x !in s2.Model()
        {
          assert x in s1.Model();
          assert x !in it1.Traversed();
        }
      }
      assert su.Model() == s1.Model() * s2.Model();
    } else {
      assert su.Model() == s1.Model() * it2.Traversed();
      assert s1.Model() !! s2.Model() - it2.Traversed() by {
        assert (forall a <- it1.Traversed(), b <- s2.Model() | b !in it2.Traversed() :: a < b);
        forall x <- s2.Model() - it2.Traversed()
          ensures x !in s1.Model()
        {
          assert x in s2.Model();
          assert x !in it2.Traversed();
        }
      }
      assert su.Model() == s1.Model() * s2.Model();
    }
  }

  // 6.97M RU
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
    requires OrdSetIntersectionModelPre(s1, s2, su)

    ensures Valid3(s1, s2, su)
    ensures OrdSetIntersectionModel(s1, s2, su)

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
      invariant fresh(s1.Repr()-old(s1.Repr()))
      invariant fresh(s2.Repr()-old(s2.Repr()))
      invariant fresh(su.Repr()-old(su.Repr()))
      invariant s1.Iterators() >= old(s1.Iterators())
      invariant s2.Iterators() >= old(s2.Iterators())
      invariant su.Iterators() >= old(su.Iterators())
    {
      it1HasPeek, it2HasPeek := Loop(s1, old(s1.Model()), it1, s2, old(s2.Model()), it2, su);
      assert Valid3It110(s1, it1, s2, it2, su);
    }
    LoopInvariantImpliesOrdSetIntersectionModel(s1, it1, s2, it2, su);
  }
}
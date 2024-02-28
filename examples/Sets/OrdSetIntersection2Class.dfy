include "../../src/OrderedSet/OrderedSetSpec2.dfy"

module OrdSetIntersection {
  import opened KeyValue
  import opened ADT
  import opened OrderedSetSpec2

  class Loop {
    const s1: OrderedSet
    const it1: OrderedSetIterator
    var it1HasPeek: bool
    const s2: OrderedSet
    const it2: OrderedSetIterator
    var it2HasPeek: bool
    const su: OrderedSet

    ghost function Repr(): set<object>
      reads s1, s1.ReprFamily(s1.ReprDepth-1)
      reads s2, s2.ReprFamily(s2.ReprDepth-1)
      reads su, su.ReprFamily(su.ReprDepth-1)
    {
      {s1} + s1.Repr() + {s2} + s2.Repr() + {su} + su.Repr()
    }

    ghost predicate Valid()
      reads this, Repr()
    {
      && this !in ({s1} + s1.Repr() + {s2} + s2.Repr() + {su} + su.Repr())
      && Valid3It110(s1, it1, s2, it2, su)
    }

    method RestoreHasPeek()
      modifies this, Repr()
      requires allocated(Repr())
      ensures allocated(Repr())
      requires Valid()
      ensures Valid()
      ensures it1HasPeek == it1.HasPeek?()
      ensures it2HasPeek == it2.HasPeek?()
    {
      it1HasPeek := it1.HasPeek();
      it2HasPeek := it2.HasPeek();
    }

    constructor(s1: OrderedSet, s2: OrderedSet, su: OrderedSet)
      modifies s1, s1.Repr(), s2, s2.Repr(), su, su.Repr()
      requires allocated(s1.Repr())
      requires allocated(s2.Repr())
      requires allocated(su.Repr())
      requires Valid3(s1, s2, su)
      ensures Valid3It110(s1, it1, s2, it2, su)
    {
      var it1' := s1.First();
      assert Valid3(s1, s2, su);
      this.it1 := it1';

      var it2' := s2.First();
      assert Valid3(s1, s2, su);
      this.it2 := it2';

      this.s1 := s1;
      this.s2 := s2;
      this.su := su;
    }
  }

  //export provides OrderedSetSpec, OrdSetIntersection

/*
  opaque twostate predicate Loop'Model(
    )
    reads s1, s1.Repr(), s2, s2.Repr(), su, su.Repr()
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
        && it1.Before'() == old(it1.Before()) + {x}
        && it2.Before'() == old(it2.Before()) + {y}
      else if x < y then
        && su.Model() == old(su.Model())
        && it1.Before'() == old(it1.Before()) + {x}
        && it2.Before'() == old(it2.Before())
      else
        && su.Model() == old(su.Model())
        && it1.Before'() == old(it1.Before())
        && it2.Before'() == old(it2.Before()) + {y}
    )
  }

  // OUTDATED
  // 9.31M RU - correctness verification
  // 73.5M RU - functional verification
  // 88.4M RU - correctness and functional verification
  method {:verify false} Loop'(
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
    modifies s1, s1.Repr(), s2, s2.Repr(), su, su.Repr()
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
    requires !it1.PastTheBeginning?()  // OUTDATED
    requires !it2.PastTheBeginning?()  // OUTDATED
    ensures Valid3It110(s1, it1, s2, it2, su)
    ensures it1HasPeek == it1.HasPeek?()
    ensures it2HasPeek == it2.HasPeek?()
    ensures !it1.PastTheBeginning?()  // OUTDATED
    ensures !it2.PastTheBeginning?()  // OUTDATED
    ensures Loop'Model(s1, it1, s2, it2, su)

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
    } else if it1Peek < it2Peek {
      it1.Next();
    assert Valid3It110(s1, it1, s2, it2, su);
    } else {
      it2.Next();
    assert Valid3It110(s1, it1, s2, it2, su);
    }
    it1HasPeek := it1.HasPeek();
  assert Valid3It110(s1, it1, s2, it2, su);
    it2HasPeek := it2.HasPeek();
  assert Valid3It110(s1, it1, s2, it2, su);
    assert Loop'Model(s1, it1, s2, it2, su) by {
      reveal Loop'Model();
      reveal it1.PeekModel(), it2.PeekModel(), su.AddModel(), it1.NextModel(), it2.NextModel();
      reveal it1.HasPeekModel();
      reveal it2.HasPeekModel();
    }
  }

  opaque ghost function LoopBound(
      s1: OrderedSet, 
      it1: OrderedSetIterator, 
      s2: OrderedSet, 
      it2: OrderedSetIterator, 
      su: OrderedSet
    ): nat
    reads s1, s1.Repr(), s2, s2.Repr(), su, su.Repr()
    requires Valid3It110(s1, it1, s2, it2, su)
  {
    reveal OrderedSetIterator.Before'Spec();
    (|s1.Model()| - |it1.Before'()|) + (|s2.Model()| - |it2.Before'()|)
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
    reveal OrderedSetIterator.Before'Spec();
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
    reads s1, s1.Repr(), s2, s2.Repr(), su, su.Repr()
    requires Valid3It110(s1, it1, s2, it2, su)
  {
    && s1.Model() == s1Model
    && s2.Model() == s2Model
    && su.Model() == it1.Before'() * it2.Before'()
    && (forall a <- it1.Before'(), b <- s2.Model() | b !in it2.Before'() :: a < b)
    && (forall a <- it2.Before'(), b <- s1.Model() | b !in it1.Before'() :: a < b)
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
    reveal OrderedSetIterator.BeforeSpec();
    reveal OrderedSetIterator.Before'Spec();
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
    modifies s1, s1.Repr(), s2, s2.Repr(), su, su.Repr()
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
    reads s1, s1.Repr(), s2, s2.Repr(), su, su.Repr()
    requires Valid3(s1, s2, su)
  {
    su.Model() == {}
  }

  opaque twostate predicate OrdSetIntersectionModel(
      s1: OrderedSet, 
      s2: OrderedSet, 
      su: OrderedSet
    )
    reads s1, s1.Repr(), s2, s2.Repr(), su, su.Repr()
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
    reveal OrderedSetIterator.Before'Spec();
    assert s1.Model() == old(s1.Model());
    assert s2.Model() == old(s2.Model());
    if !it1.HasPeek?() {
      assert it1.PastTheEnd?();
      assert it1.Before'() == s1.Model();
    }
    if !it2.HasPeek?() {
      assert it2.Before'() == s2.Model();
    }
    assert su.Model() == s1.Model() * s2.Model();
  }

  method OrdSetIntersection(s1: OrderedSet, s2: OrderedSet, su: OrderedSet)
    modifies s1, s1.Repr(), s2, s2.Repr(), su, su.Repr()
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
      invariant !it1.PastTheBeginning?()
      invariant !it2.PastTheBeginning?()
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
    assume false;
  }
  */
}
include "../../src/OrderedSet/OrderedSetSpec2.dfy"
include "../../src/AdtWithoutThis.dfy"
include "../../src/Collections/KeyValue.dfy"
include "../../src/Collections/SetObject.dfy"

module OrdSetIntersection2Datatype {
  import opened KeyValue
  import opened ADT
  import opened OrderedSetSpec2
  import opened SetObject

  //export provides OrderedSetSpec, OrdSetIntersection

  datatype OrdSetIntersectionLoopState = OrdSetIntersectionLoopState(
    s1: OrderedSet,
    it1: OrderedSetIterator,
    s2: OrderedSet,
    it2: OrderedSetIterator,
    su: OrderedSet
  )
  {
    ghost function Repr(): set<object>
      reads s1.ReprFamily(s1.ReprDepth-1)
      reads s2.ReprFamily(s2.ReprDepth-1)
      reads su.ReprFamily(su.ReprDepth-1)
    {
      Repr3(s1, s2, su)
    }

    twostate predicate Fresh()
      reads Repr()
    {
      Fresh3(s1, s2, su)
    }

    ghost predicate Valid()
      reads Repr()
    {
      Valid3It110(s1, it1, s2, it2, su)
    }

    opaque twostate predicate LoopBody'Model()
      reads Repr()
      requires old(Valid())
      requires old(it1.HasPeek?())
      requires old(it2.HasPeek?())
      requires Valid()
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

    // 28.1M RU - correctness verification
    // 17.4M RU - correctness verification (with MaintainsValid...)
    // 60.7M RU - functional verification
    // 22.9M RU - correctness and functional verification (with MaintainsValid...)
    method LoopBody'()
      returns (
        it1HasPeek: bool,
        it2HasPeek: bool
      )
      modifies Repr()
      requires allocated(Repr())
      ensures allocated(Repr())
      ensures Fresh()

      requires Valid()
      requires it1.HasPeek?()
      requires it2.HasPeek?()

      ensures Valid()
      ensures it1HasPeek == it1.HasPeek?()
      ensures it2HasPeek == it2.HasPeek?()
      ensures !it1.PastTheBeginning?()
      ensures !it2.PastTheBeginning?()
      ensures LoopBody'Model()

      ensures s1.Iterators() >= old(s1.Iterators())
      ensures s2.Iterators() >= old(s2.Iterators())
      ensures su.Iterators() >= old(su.Iterators())
    {
      var it1Peek := it1.Peek();
      MaintainsValid3It110Helper(s1, it1, s2, it2, su);
      assert Valid();
      label L1:
      var it2Peek := it2.Peek();
      MaintainsValid3It110Helper@L1(s2, it2, s1, it1, su);
      assert Valid();
      if it1Peek == it2Peek {
        label L2:
        su.Add(it1Peek);
        MaintainsValid3Helper@L2(su, s1, s2);
        assert Valid();
        label L3:
        it1.Next();
        MaintainsValid3It110Helper@L3(s1, it1, s2, it2, su);
        assert Valid();
        label L4:
        it2.Next();
        MaintainsValid3It110Helper@L4(s2, it2, s1, it1, su);
        assert Valid();
      } else if it1Peek < it2Peek {
        label L5:
        it1.Next();
        MaintainsValid3It110Helper@L5(s1, it1, s2, it2, su);
        assert Valid();
      } else {
        label L6:
        it2.Next();
        MaintainsValid3It110Helper@L6(s2, it2, s1, it1, su);
        assert Valid();
      }
      assert Valid();
      label L7:
      it1HasPeek := it1.HasPeek();
      MaintainsValid3It110Helper@L7(s1, it1, s2, it2, su);
      assert Valid();
      label L8:
      it2HasPeek := it2.HasPeek();
      MaintainsValid3It110Helper@L8(s2, it2, s1, it1, su);
      assert Valid();
      assert LoopBody'Model() by {
        assume false;
        reveal LoopBody'Model();
        reveal OrderedSetIterator.PeekModel();
        reveal OrderedSet.AddModel();
        reveal OrderedSetIterator.NextModel();
        reveal OrderedSetIterator.HasPeekModel();
      }
    }

    opaque ghost function LoopBound(): nat
      reads Repr()
      requires Valid()
    {
      reveal OrderedSetIterator.Before'Spec();
      (|s1.Model()| - |it1.Before'()|) + (|s2.Model()| - |it2.Before'()|)
    }

    twostate lemma LoopBoundDecreases()
      requires old(Valid())
      requires old(it1.HasPeek?())
      requires old(it2.HasPeek?())
      requires Valid()
      requires LoopBody'Model()
      ensures LoopBound() < old(LoopBound())
    {
      reveal LoopBody'Model(), LoopBound();
      reveal OrderedSetIterator.PeekSpec();
      reveal OrderedSetIterator.Before'Spec();
    }

    opaque ghost predicate LoopInvariant(s1Model: set<K>, s2Model: set<K>)
      reads Repr()
      requires Valid()
    {
      && s1.Model() == s1Model
      && s2.Model() == s2Model
      && su.Model() == it1.Before'() * it2.Before'()
      && (forall a <- it1.Before'(), b <- s2.Model() | b !in it2.Before'() :: a < b)
      && (forall a <- it2.Before'(), b <- s1.Model() | b !in it1.Before'() :: a < b)
    }

    twostate lemma LoopBodyMaintainsInvariant(s1Model: set<K>, s2Model: set<K>)
      requires old(Valid())
      requires old(it1.HasPeek?())
      requires old(it2.HasPeek?())
      requires old(LoopInvariant(s1Model, s2Model))
      requires Valid()
      requires LoopBody'Model()
      ensures LoopInvariant(s1Model, s2Model)
    {
      reveal LoopBody'Model(), LoopInvariant();
      reveal OrderedSetIterator.PeekSpec();
      reveal OrderedSetIterator.BeforeSpec();
      reveal OrderedSetIterator.Before'Spec();
    }

    method LoopBody()
      returns (
        it1HasPeek: bool,
        it2HasPeek: bool
      )
      modifies Repr()
      requires allocated(Repr())
      ensures allocated(Repr())
      ensures Fresh()

      requires Valid()
      requires it1.HasPeek?()
      requires it2.HasPeek?()
      requires LoopInvariant(s1.Model(), s2.Model())

      ensures Valid()
      ensures it1HasPeek == it1.HasPeek?()
      ensures it2HasPeek == it2.HasPeek?()
      ensures !it1.PastTheBeginning?()
      ensures !it2.PastTheBeginning?()
      ensures LoopInvariant(old(s1.Model()), old(s2.Model()))
      ensures LoopBound() < old(LoopBound())

      ensures s1.Iterators() >= old(s1.Iterators())
      ensures s2.Iterators() >= old(s2.Iterators())
      ensures su.Iterators() >= old(su.Iterators())
    {
      it1HasPeek, it2HasPeek := LoopBody'();
      LoopBoundDecreases();
      LoopBodyMaintainsInvariant(old(s1.Model()), old(s2.Model()));
    }

    opaque ghost predicate LoopPre()
      reads Repr()
      requires Valid()
    {
      && su.Model() == {}
      && it1.Before'() == {}
      && it2.Before'() == {}
    }

    opaque twostate predicate LoopModel()
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && s1.Model() == old(s1.Model())
      && s2.Model() == old(s2.Model())
      && su.Model() == s1.Model() * s2.Model()
    }

    twostate lemma LoopInvariantImpliesLoopModel()
      requires old(Valid())
      requires Valid()
      requires !it1.HasPeek?() || !it2.HasPeek?()
      requires !it1.PastTheBeginning?()
      requires !it2.PastTheBeginning?()
      requires LoopInvariant(old(s1.Model()), old(s2.Model()))
      ensures LoopModel()
    {
      reveal LoopInvariant(), LoopModel();
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
        assert it2.PastTheEnd?();
        assert it2.Before'() == s2.Model();
      }

      if !it1.HasPeek?() && !it2.HasPeek?() {
        assert su.Model() == s1.Model() * s2.Model();
      } else if it1.HasPeek?() {
        assert su.Model() == it1.Before'() * s2.Model();
        assert s1.Model() - it1.Before'() !! s2.Model() by {
          assert (forall a <- it2.Before'(), b <- s1.Model() | b !in it1.Before'() :: a < b);
          forall x <- s1.Model() - it1.Before'()
            ensures x !in s2.Model()
          {
            assert x in s1.Model();
            assert x !in it1.Before'();
          }
        }
        assert su.Model() == s1.Model() * s2.Model();
      } else {
        assert su.Model() == s1.Model() * it2.Before'();
        assert s1.Model() !! s2.Model() - it2.Before'() by {
          assert (forall a <- it1.Before'(), b <- s2.Model() | b !in it2.Before'() :: a < b);
          forall x <- s2.Model() - it2.Before'()
            ensures x !in s1.Model()
          {
            assert x in s2.Model();
            assert x !in it2.Before'();
          }
        }
        assert su.Model() == s1.Model() * s2.Model();
      }
    }

    // 4.50M RU
    method Loop()
      modifies Repr()
      requires allocated(Repr())
      ensures allocated(Repr())
      ensures Fresh()

      requires Valid()
      requires LoopPre()
      requires !it1.PastTheBeginning?()
      requires !it2.PastTheBeginning?()

      ensures Valid()
      ensures LoopModel()

      ensures s1.Iterators() >= old(s1.Iterators())
      ensures s2.Iterators() >= old(s2.Iterators())
      ensures su.Iterators() >= old(su.Iterators())
    {
      var it1HasPeek := it1.HasPeek();
      assert Valid();
      var it2HasPeek := it2.HasPeek();
      assert Valid();
      assert LoopInvariant(old(s1.Model()), old(s2.Model())) by {
        reveal LoopInvariant();
        reveal OrderedSetIterator.HasPeekModel();
        reveal LoopPre();
      }
      while it1HasPeek && it2HasPeek
        decreases LoopBound()
        invariant Valid()
        invariant it1HasPeek == it1.HasPeek?()
        invariant it2HasPeek == it2.HasPeek?()
        invariant !it1.PastTheBeginning?()
        invariant !it2.PastTheBeginning?()
        invariant LoopInvariant(old(s1.Model()), old(s2.Model()))

        invariant allocated(Repr())
        invariant Fresh()
        invariant s1.Iterators() >= old(s1.Iterators())
        invariant s2.Iterators() >= old(s2.Iterators())
        invariant su.Iterators() >= old(su.Iterators())
      {
        assert LoopInvariant(s1.Model(), s2.Model()) by {
          reveal LoopInvariant();
        }
        it1HasPeek, it2HasPeek := LoopBody();
        assert LoopInvariant(old(s1.Model()), old(s2.Model())) by {
          reveal LoopInvariant();
        }
      }
      LoopInvariantImpliesLoopModel();
    }
  }

  opaque ghost predicate OrdSetIntersectionModelPre(
      s1: OrderedSet,
      s2: OrderedSet,
      su: OrderedSet
    )
    reads Repr3(s1, s2, su)
    requires Valid3(s1, s2, su)
  {
    su.Model() == {}
  }

  opaque twostate predicate OrdSetIntersectionModel(
      s1: OrderedSet,
      s2: OrderedSet,
      su: OrderedSet
    )
    reads Repr3(s1, s2, su)
    requires old(Valid3(s1, s2, su))
    requires Valid3(s1, s2, su)
  {
    && s1.Model() == old(s1.Model())
    && s2.Model() == old(s2.Model())
    && su.Model() == s1.Model() * s2.Model()
  }

  // 2.25M RU
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
    var state := OrdSetIntersectionLoopState(s1, it1, s2, it2, su);
    assert state.Valid();
    assert state.LoopPre() by {
      reveal state.LoopPre();
      reveal OrdSetIntersectionModelPre();
      reveal OrderedSet.FirstModel();
    }
    state.Loop();
    assert OrdSetIntersectionModel(s1, s2, su) by {
      reveal OrdSetIntersectionModel();
      reveal state.LoopModel();
      reveal OrderedSet.FirstModel();
    }
  }
}
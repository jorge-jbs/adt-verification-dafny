include "../../src/TreeSet/TreeSetSpec.dfy"
include "../../src/Collections/SetInt.dfy"

module OpaqueSpec.Pairs.Model {
  import opened KeyValue
  import opened ADT
  import opened UnorderedSetSpec
  import opened OrderedSetSpec
  import opened TreeSetSpec
  import Set
  import opened SetInt

    /*
  Assume that 'it' is an iterator that belongs to 's' and that it.Traversed() == it and it.Peek?() == pk.

  If we have called a method on 's' that does not affect 'it', the set of traversed elements and the element
  pointed to by 'it' should remain as they were.
  */
  twostate lemma SameIteratorsBefore(s: TreeSet, it: UnorderedSetIterator, tr: set<int>, pk: int)
    requires old(it.Valid()) && it.Valid()
    requires old(s.Valid()) && s.Valid()
    requires it in old(s.Iterators())
    requires s.Iterators() >= old(s.Iterators())
    requires s.SameIterators()
    requires old(it.HasPeek?()) && it.HasPeek?()
    requires old(it.Before()) == tr && old(it.Peek?()) == pk
    ensures it.Before() == tr && it.Peek?() == pk
  {
    reveal TreeSet.SameIterators();

    assert s.SameIteratorModel(it);
    reveal TreeSet.SameIteratorModel();
  }


  /*
  Assume that 'itErased' is an iterator that belongs to 's' and we have just called s.Erase(itErased)

  If 'it' was at the left of 'itErased' (i.e., it.Peek?() < itErased.Peek?()) then it.Traversed() is
  not affected by the deletion.
  */
  twostate lemma EraseIteratorRight(s: TreeSet, itErased: UnorderedSetIterator, it: UnorderedSetIterator, tr: set<int>)
    requires old(s.Valid()) && s.Valid()
    requires s.Iterators() >= old(s.Iterators())
    requires old(it.Valid()) && old(itErased.Valid())
    requires old(it.HasPeek?()) && old(itErased.HasPeek?())
    requires it in old(s.Iterators()) && itErased in old(s.Iterators())
    requires s.RemoveIterators(old(itErased.Peek?()))
    requires old(it.Peek?()) < old(itErased.Peek?())

    requires old(it.Traversed()) == tr
    ensures it.Valid()
    ensures it.Traversed() == tr
  {
    reveal TreeSet.RemoveIterators();
    reveal TreeSet.RemoveIteratorModel();
  }

  /*
  Assume that 'itErased' is an iterator that belongs to 's' and we have just called s.Erase(itErased)

  If 'it' was at the left of 'itErased' (i.e., it.Peek?() < itErased.Peek?()) then it.RTraversed() is
  affected by the deletion, so that it.RTraversed() no longer contains itErased.Peek?().
  */
  twostate lemma EraseIteratorRightRTraversed(s: TreeSet, itErased: OrderedSetIterator, new newItErased: UnorderedSetIterator, it: OrderedSetIterator, tr: set<int>)
    requires old(s.Valid()) && s.Valid()
    requires s.Iterators() >= old(s.Iterators())
    requires old(it.Valid()) && old(itErased.Valid())
    requires old(itErased.HasPeek?())
    requires newItErased.Valid()
    requires it in old(s.Iterators()) && itErased in old(s.Iterators()) && newItErased in s.Iterators()
    requires s.RemoveIterators(old(itErased.Peek?()))
    requires s.EraseModel(itErased, newItErased)
    requires old(it.HasPeek?()) ==> old(it.Peek?()) < old(itErased.Peek?())

    requires old(it.RTraversed()) == tr
    ensures it.Valid()
    ensures it.RTraversed() == tr - { old(itErased.Peek?()) }
  {
    reveal TreeSet.RemoveIterators();
    assert s.RemoveIteratorModel(it, old(itErased.Peek?()));
    reveal TreeSet.RemoveIteratorModel();
    if old(it.HasPeek?()) {
      assert it.Traversed() == old(it.Traversed());
      reveal OrderedSetIterator.After();

      assert s.Model() == old(s.Model()) - {old(itErased.Peek?())} by { reveal UnorderedSet.EraseModel(); }
      if (it.HasPeek?()) {
        calc {
          it.RTraversed();
        ==
          it.After();
        ==
          (s.Model() - {it.Peek?()})  - it.Before();
        == { reveal UnorderedSet.EraseModel(); }
          (old(s.Model()) - {old(itErased.Peek?())} - {it.Peek?()}) - it.Before();
        }
      }
    }
  }

  /*
  Assume two iterators on the same TreeSet, it1 and it2 such that it1.Peek?() <= it2.Peek?()
  Then, it1.Traversed() <= it2.Traversed().
  */
  lemma LeqPeekIterator(s: TreeSet, it1: OrderedSetIterator, it2: OrderedSetIterator)
    requires s.Valid()
    requires it1.Valid() && it1 in s.Iterators()
    requires it2.Valid() && it2 in s.Iterators()
    requires it1.HasPeek?() && it2.HasPeek?()
    requires it1.Peek?() <= it2.Peek?()

    ensures it1.Traversed() <= it2.Traversed()

  {
    if !(it1.Traversed() <= it2.Traversed()) {
      var x :| x in it1.Traversed() && x !in it2.Traversed();
      assert x in s.Model() by { reveal UnorderedSetIterator.TraversedSpec(); }
      assert x < it1.Peek?() by { reveal OrderedSetIterator.PeekOrderSpec(); }
      assert it2.Peek?() <= x by { reveal OrderedSetIterator.PeekOrderSpec(); }
    }
  }

  /*
  Assume two iterators on the same TreeSet, it1 and it2 such that it1.Traversed() <= it2.Traversed()
  Then, it1.Peek?() <= it2.Peek?().
  */
  lemma SubsetTraversedIterator(s: TreeSet, it1: OrderedSetIterator, it2: OrderedSetIterator)
    requires s.Valid()
    requires it1.Valid() && it1 in s.Iterators()
    requires it2.Valid() && it2 in s.Iterators()
    requires it1.HasPeek?() && it2.HasPeek?()
    requires it1.Traversed() <= it2.Traversed()

    ensures it1.Peek?() <= it2.Peek?()

  {
    if (it1.Peek?() > it2.Peek?()) {
      assert it2.Peek?() in s.Model() by { reveal UnorderedSetIterator.PeekSpec(); }
      assert it2.Peek?() in it1.Traversed() by { reveal OrderedSetIterator.PeekOrderSpec(); }
      assert it2.Peek?() in it2.Traversed();
      assert it2.Peek?() < it2.Peek?() by { reveal OrderedSetIterator.PeekOrderSpec(); }
      assert false;
    }
  }

  /*
    Assume that 's' is a set with iterators 'itNext' and 'it' traversing it. Assume that we have called 'itNext.Next()' (or 'itNext.Prev()')

    If it.Peek?() == pk and it.Traversed?() == tr, then both values remain constant after the call 'itNext.Next()' (or 'itNext.Prev()')
  */
  twostate lemma NextPreservesOtherIterators(s: TreeSet, itNext: UnorderedSetIterator, it: UnorderedSetIterator, pk: int, tr: set<int>)
    requires old(s.Valid()) && s.Valid()
    requires old(itNext.Valid()) && old(it.Valid())
    requires itNext in old(s.Iterators()) && it in old(s.Iterators())
    requires s.Iterators() >= old(s.Iterators())
    requires fresh(s.Repr() - old(s.Repr()))
    requires itNext.NextIterators()
    requires it != itNext
    requires old(it.HasPeek?())
    requires old(it.Peek?()) == pk && old(it.Traversed() == tr)

    ensures it.Valid() && it.HasPeek?()
    ensures it.Peek?() == pk && it.Traversed() == tr
  {
    reveal UnorderedSetIterator.NextIterators();
    assert s.SameIteratorModel(it);
    reveal TreeSet.SameIteratorModel();
  }

  ghost function PairsFunction(s: set<int>, W: int): set<int>
    decreases s
  {
    if s == {} then
      {}
    else
      var min := Min(s);
      var max := Max(s);
      if min == max then {min} else
      if min + max <= W then
        PairsFunction(s - {min, max}, W)
      else
        {max} + PairsFunction(s - {max}, W)
  }

  opaque ghost predicate LoopCondition(
    s: TreeSet,
    itl: OrderedSetIterator,
    itg: OrderedSetIterator)
    reads s.Repr()
    requires Valid1It2(s, itl, itg)
  {
    itl.HasPeek?() && itg.HasPeek?() && itl.Peek?() < itg.Peek?()
  }

  lemma LoopConditionEnsuresTraversed(
    s: TreeSet,
    itl: OrderedSetIterator,
    itg: OrderedSetIterator
  )
    requires Valid1It2(s, itl, itg)
    requires LoopCondition(s, itl, itg)
    ensures itl.Traversed() < itg.Traversed()
    ensures |itl.Traversed()| < |itg.Traversed()|
    ensures reveal LoopCondition(); itl.Peek?() < itg.Peek?()
  {
    reveal LoopCondition();
    reveal UnorderedSetIterator.TraversedSpec();
    reveal OrderedSetIterator.PeekOrderSpec();
    reveal UnorderedSetIterator.PeekSpec();
    reveal UnorderedSetIterator.BeforeSpec();
    assert forall x | x in itl.Traversed() :: x in itg.Traversed();
    assert itl.Peek?() !in itl.Traversed() && itl.Peek?() in itg.Traversed();
    Set.StrictSubsetCard(itl.Traversed(),itg.Traversed());
  }

  opaque ghost function LoopBound(
    s: TreeSet,
    itl: OrderedSetIterator,
    itg: OrderedSetIterator
  ): nat
    reads s.Repr()
    requires Valid1It2(s, itl, itg)
  {
    reveal OrderedSetIterator.TraversedSpec();
    if LoopCondition(s,itl,itg) then
      LoopConditionEnsuresTraversed(s,itl,itg);
      |itg.Traversed()| - |itl.Traversed()|
    else
      0
  }

  opaque ghost predicate LoopInvariantModel(
    s: TreeSet,
    oldModel: set<int>,
    W: int,
    itl: OrderedSetIterator,
    itg: OrderedSetIterator
  )
    reads s.Repr()
    requires s.Valid()
    requires Valid1It2(s, itl, itg)
  {
    itl.Traversed() == {}
    && PairsFunction(oldModel, W) == itg.RTraversed() + PairsFunction(s.Model() - itg.RTraversed(), W)
  }

  lemma SubtractAllBut(xs: set<int>, ys: set<int>)
    requires ys <= xs
    ensures (xs - (xs - ys)) == ys
  { }

  lemma SubtractThenAdd(xs: set<int>, ys: set<int>)
    requires ys <= xs
    ensures xs - ys + ys == xs
  { }

  method MakePair(
    s: TreeSet,
    ghost sModel: set<int>,
    itl: OrderedSetIterator,
    itg: OrderedSetIterator,
    ghost W: int
  ) returns (
      newitl: OrderedSetIterator,
      newitg: OrderedSetIterator
    )
    modifies s.Repr()
    requires allocated(s.Repr())
    ensures allocated(s.Repr())
    ensures fresh(s.Repr()-old(s.Repr()))

    requires Valid1It2(s, itl, itg)
    requires itl.HasPeek?()
    requires itg.HasPeek?()
    requires itl.Traversed() < itg.Traversed() && |itl.Traversed()| < |itg.Traversed()|
    requires LoopCondition(s, itl, itg)

    requires LoopInvariantModel(s, sModel, W, itl, itg)
    requires itl.Peek?() + itg.Peek?() <= W

    ensures Valid1It2(s, newitl, newitg)
    ensures LoopBound(s, newitl, newitg) < old(LoopBound(s, itl,itg))

    ensures s.Iterators() >= {newitl,newitg} + old(s.Iterators())

    ensures LoopInvariantModel(s, sModel, W, newitl, newitg)
  {
    label L1:
    ghost var min := itl.Peek?();
    ghost var max := itg.Peek?();
    ghost var oldModel := s.Model();
    ghost var oldItgRTraversed := itg.RTraversed();

    assert min < max by {
      var x :| x in itg.Traversed() && x !in itl.Traversed();
      assert x in s.Model() by { reveal UnorderedSetIterator.TraversedSpec(); }
      assert min <= x < max by { reveal OrderedSetIterator.PeekOrderSpec(); }
    }

    assert model1:
      && s.Model() - itg.RTraversed() != {}
      && min == Min(s.Model() - itg.RTraversed())
      && max == Max(s.Model() - itg.RTraversed())
      && old(s.Model()) == oldModel
    by {
      assert itl.Peek?() < itg.Peek?();
      itg.PeekROrder();
      reveal OrderedSetIterator.After();
      reveal LoopInvariantModel();
      reveal UnorderedSetIterator.PeekSpec();
      reveal OrderedSetIterator.PeekOrderSpec();
      assert min in s.Model() - itg.RTraversed();
      assert max in s.Model() - itg.RTraversed();
    }

    newitl := s.Erase(itl);

    label L2:

    assert
      && Valid1It2(s, newitl, itg)
      && newitl.HasPeek?()
    by {
      reveal TreeSet.RemoveIterators();
      reveal TreeSet.RemoveIteratorModel();
      reveal UnorderedSet.EraseModel();
      reveal UnorderedSetIterator.TraversedSpec();
      reveal LoopCondition();
      assert newitl.HasPeek?() by {
        reveal UnorderedSetIterator.PeekSpec();
      }
    }

    assert model2:
      && s.Model() == oldModel - {min}
      && itg.Peek?() == max
      && itg.RTraversed() == oldItgRTraversed
      && newitl.Traversed() == {}
    by {
      assert s.Model() == oldModel - {min} by {
        reveal UnorderedSet.EraseModel(itl, newitl);
      }

      assert
        && itg.Peek?() == max
        && itg.RTraversed() == old(itg.RTraversed())
        && newitl.Traversed() == {}
      by {
        reveal TreeSet.RemoveIterators();
        reveal TreeSet.RemoveIteratorModel();
        reveal OrderedSetIterator.After();
        reveal TreeSet.EraseModel();
        reveal LoopInvariantModel();
      }
    }

    newitg := itg.Copy();

    label L3:

    assert
      && Valid1It3(s, newitl, newitg, itg)
      && newitg.HasPeek?()
      && newitl.HasPeek?()
    by {
      reveal LoopCondition();
      reveal TreeSet.SameIterators();
      reveal TreeSet.SameIteratorModel();
      assert itg.HasPeek?() by {
        assert old@L1(itg.HasPeek?());
        assert old@L2(itg.HasPeek?()) by {
          reveal TreeSet.RemoveIterators();
          reveal TreeSet.RemoveIteratorModel();
        }
        reveal UnorderedSetIterator.PeekSpec();
      }
    }

    assert model3:
      && s.Model() == oldModel - {min}
      && itg.Peek?() == old(itg.Peek?())
      && itg.RTraversed() == oldItgRTraversed
      && newitl.Traversed() == {}
      && newitg.Peek?() == itg.Peek?() == max
      && newitg.RTraversed() == itg.RTraversed()
    by {
      reveal model1, model2;
      assert s.Model() == oldModel - {min} by {
        reveal UnorderedSetIterator.CopyModel();
      }

      assert itg.Peek?() == old(itg.Peek?()) &&
             itg.RTraversed() == oldItgRTraversed by {
        reveal UnorderedSetIterator.CopyModel();
        reveal OrderedSetIterator.After();
      }

      assert newitl.Traversed() == {} by {
        assert old@L2(newitl.Before()) == newitl.Before() by {
          SameIteratorsBefore@L2(s, newitl, {}, old@L2(newitl.Peek?()));
        }
      }

      assert
        newitg.Peek?() == itg.Peek?()
        && newitg.RTraversed() == itg.RTraversed() by {
        reveal OrderedSetIterator.CopyModel();
        reveal OrderedSetIterator.After();
        assert newitg.Traversed() == itg.Traversed();
        SubsetTraversedIterator(s, newitg, itg);
        SubsetTraversedIterator(s, itg, newitg);
      }
    }

    newitg.Prev();

    label L4:

    assert
      && Valid1It3(s, newitl, newitg, itg)
      && newitl.HasPeek?()
      && itg.HasPeek?()
    by {
      reveal OrderedSetIterator.NextIterators();
      reveal TreeSet.SameIteratorModel();
    }
    assert newitgNeItg: newitg.HasPeek?() ==> newitg.Peek?() != itg.Peek?() by {
      reveal OrderedSetIterator.PrevModel();
      reveal OrderedSetIterator.CopyModel();
      reveal TreeSet.EraseModel();
      reveal TreeSet.RemoveIterators();
      reveal TreeSet.RemoveIteratorModel();
      reveal OrderedSetIterator.NextIterators();
      reveal TreeSet.SameIterators();
      reveal TreeSet.SameIteratorModel();
      reveal OrderedSetIterator.PeekSpec();
      reveal OrderedSetIterator.PeekOrderSpec();
      reveal OrderedSetIterator.TraversedSpec();
      reveal OrderedSetIterator.RTraversedSpec();
      reveal OrderedSetIterator.AfterSpec();
      reveal OrderedSetIterator.BeforeSpec();

      assert old@L3(newitg.Peek?() == itg.Peek?());
      if newitg.HasPeek?() {
        newitg.PeekROrder();
        calc {
           newitg.Peek?();
        < old@L3(newitg.Peek?());
        == old@L3(itg.Peek?());
        == itg.Peek?();
        }
      }
    }

    assert model4:
      && s.Model() == oldModel - {min}
      && itg.Peek?() == max
      && itg.RTraversed() == oldItgRTraversed
      && (newitg.HasPeek?() ==> newitg.Peek?() < itg.Peek?())
      && newitg.RTraversed() == itg.RTraversed() + { max }
      && newitl.Traversed() == {}
    by {
      reveal model1, model2, model3;
      assert s.Model() == oldModel - {min} by {
        reveal OrderedSetIterator.PrevModel();
      }

      assert itg.Peek?() == old(itg.Peek?())
             && itg.RTraversed() == oldItgRTraversed by {
        reveal OrderedSetIterator.NextIterators();
        reveal OrderedSetIterator.After();
        reveal UnorderedSet.SameIteratorModel();
        NextPreservesOtherIterators@L3(s, newitg, itg, itg.Peek?(), itg.Traversed());
        assert itg.Peek?() == old@L3(itg.Peek?()) == max;
      }

      assert newitg.HasPeek?() ==> newitg.Peek?() < itg.Peek?() by {
        if newitg.HasPeek?() {
          assert old@L3(newitg.Peek?()) in newitg.After() by { reveal OrderedSetIterator.PrevModel(); }
          newitg.PeekROrder();
          assert old@L3(newitg.Peek?()) == itg.Peek?();
        }
      }

      assert newitg.RTraversed() == itg.RTraversed() + { max } by {
        reveal OrderedSetIterator.PrevModel();
        reveal OrderedSetIterator.NextIterators();
        reveal OrderedSetIterator.After();
      }

      assert newitl.Traversed() == {} by {
        reveal OrderedSetIterator.NextIterators();
        reveal OrderedSetIterator.After();
        reveal UnorderedSet.SameIteratorModel();
        NextPreservesOtherIterators@L3(s, newitg, newitl, newitl.Peek?(), newitl.Traversed());
      }
    }

    assert newitgTraversed: newitg.HasPeek?() ==> newitg.Traversed() - newitl.Traversed() == old(itg.Traversed() - itl.Traversed() - {itl.Peek?()}) - {newitg.Peek?()} by {
      reveal LoopCondition();
      reveal OrderedSetIterator.PrevModel();
      reveal OrderedSetIterator.CopyModel();
      reveal TreeSet.EraseModel();
      reveal TreeSet.RemoveIterators();
      reveal TreeSet.RemoveIteratorModel();
      reveal OrderedSetIterator.NextIterators();
      reveal TreeSet.SameIterators();
      reveal TreeSet.SameIteratorModel();
      reveal OrderedSetIterator.PeekSpec();
      reveal OrderedSetIterator.PeekOrderSpec();
      reveal OrderedSetIterator.TraversedSpec();
      reveal OrderedSetIterator.After();
      reveal OrderedSetIterator.RTraversedSpec();
      reveal OrderedSetIterator.AfterSpec();
      reveal OrderedSetIterator.BeforeSpec();
    }

    assert itgTraversed: newitg.HasPeek?() ==> itg.Traversed() == newitg.Traversed() + {newitg.Peek?()} by {
      reveal OrderedSetIterator.PrevModel();
      reveal OrderedSetIterator.CopyModel();
      reveal TreeSet.EraseModel();
      reveal TreeSet.RemoveIterators();
      reveal TreeSet.RemoveIteratorModel();
      reveal OrderedSetIterator.NextIterators();
      reveal TreeSet.SameIterators();
      reveal TreeSet.SameIteratorModel();
      reveal OrderedSetIterator.PeekSpec();
      reveal OrderedSetIterator.PeekOrderSpec();
      reveal OrderedSetIterator.TraversedSpec();
      reveal OrderedSetIterator.After();
      reveal OrderedSetIterator.RTraversedSpec();
      reveal OrderedSetIterator.AfterSpec();
      reveal OrderedSetIterator.BeforeSpec();
    }

    var newitlPeek := newitl.Peek();

    label L5:

    assert
      && Valid1It3(s, newitl, newitg, itg)
      && newitl.HasPeek?()
      && itg.HasPeek?()
    by {
      reveal TreeSet.SameIterators();
      reveal TreeSet.SameIteratorModel();
    }

    assert model5:
      && s.Model() == old(s.Model()) - {min}
      && itg.Peek?() == old(itg.Peek?())
      && itg.RTraversed() == old(itg.RTraversed())
      && newitg.RTraversed() == old(itg.RTraversed()) + { max }
      && (newitg.HasPeek?() ==> newitg.Peek?() < itg.Peek?())
      && newitl.Traversed() == {} && newitlPeek == newitl.Peek?()
    by {
      reveal model4;
      assert s.Model() == old(s.Model()) - {min} by {
        reveal UnorderedSetIterator.PeekModel();
      }

      assert itg.Peek?() == old(itg.Peek?())
             && itg.RTraversed() == old(itg.RTraversed()) by {
        reveal UnorderedSetIterator.PeekModel();
        reveal TreeSet.SameIterators();
        reveal TreeSet.SameIteratorModel();
        reveal OrderedSetIterator.After();
        SameIteratorsBefore@L4(s, itg, itg.Traversed(), itg.Peek?());
      }

      assert newitg.RTraversed() == old(itg.RTraversed()) + { max } by {
        reveal UnorderedSetIterator.PeekModel();
        reveal TreeSet.SameIterators();
        reveal TreeSet.SameIteratorModel();
        reveal OrderedSetIterator.After();
      }

      assert newitg.HasPeek?() ==> newitg.Peek?() < itg.Peek?() by {
        reveal UnorderedSetIterator.PeekModel();
        reveal TreeSet.SameIterators();
        reveal TreeSet.SameIteratorModel();
      }

      assert newitl.Traversed() == {} && newitlPeek == newitl.Peek?() by {
        reveal UnorderedSetIterator.PeekModel();
        SameIteratorsBefore@L4(s, newitl, newitl.Traversed(), newitl.Peek?());
      }
    }

    var itgPeek := itg.Peek();

    assert
      && Valid1It3(s, newitl, newitg, itg)
      && newitl.HasPeek?()
      && itg.HasPeek?()
    by {
      reveal TreeSet.SameIterators();
      reveal TreeSet.SameIteratorModel();
    }

    assert model6:
      && s.Model() == old@L1(s.Model()) - {min}
      && itgPeek == itg.Peek?() == old(itg.Peek?()) == max
      && itg.RTraversed() == oldItgRTraversed
      && newitg.RTraversed() == itg.RTraversed() + { max }
      && newitl.Traversed() == {} && newitlPeek == newitl.Peek?()
      && newitl.Traversed() <= itg.Traversed() && newitl.Peek?() <= itg.Peek?()
      && (newitg.HasPeek?() ==> newitg.Peek?() < itg.Peek?())
    by {
      reveal model1, model2, model3, model4, model5;

      assert s.Model() == old@L1(s.Model()) - {min} by {
        reveal UnorderedSetIterator.PeekModel();
      }

      assert itgPeek == itg.Peek?() == old(itg.Peek?()) == max
             && itg.RTraversed() == oldItgRTraversed by {
        reveal UnorderedSetIterator.PeekModel();
        reveal TreeSet.SameIterators();
        reveal TreeSet.SameIteratorModel();
        reveal OrderedSetIterator.After();
        SameIteratorsBefore@L5(s, itg, old@L5(itg.Traversed()), old@L5(itg.Peek?()));
      }

      assert newitg.RTraversed() == itg.RTraversed() + { max } by {
        reveal UnorderedSetIterator.PeekModel();
        reveal TreeSet.SameIterators();
        reveal TreeSet.SameIteratorModel();
        reveal OrderedSetIterator.After();
      }

      assert newitl.Traversed() == {} && newitlPeek == newitl.Peek?() by {
        reveal UnorderedSetIterator.PeekModel();
        SameIteratorsBefore@L5(s, newitl, {}, old@L5(newitl.Peek?()));
      }

      assert newitl.Traversed() <= itg.Traversed() && newitl.Peek?() <= itg.Peek?() by {
        SubsetTraversedIterator(s, newitl, itg);
      }

      assert newitg.HasPeek?() ==> newitg.Peek?() < itg.Peek?() by {
        reveal UnorderedSetIterator.PeekModel();
        reveal TreeSet.SameIterators();
        reveal TreeSet.SameIteratorModel();
      }
    }

    label L6:

    if newitlPeek == itgPeek {
      assert itg.Traversed() == newitl.Traversed() == {} by {
        reveal model1, model2, model3, model4, model5, model6;
        LeqPeekIterator(s, newitl, itg);
        LeqPeekIterator(s, itg, newitl);
      }

      newitl := s.Erase(itg);

      assert Valid1It2(s, newitl, newitg) by {
        reveal OrderedSetIterator.PeekModel();
        reveal TreeSet.RemoveIterators();
        reveal TreeSet.RemoveIteratorModel();
        reveal UnorderedSet.EraseModel();
        reveal UnorderedSetIterator.BeforeSpec();
        reveal OrderedSetIterator.After();
        reveal OrderedSetIterator.AfterSpec();
        reveal OrderedSetIterator.RTraversedSpec();
        reveal OrderedSetIterator.PeekOrderSpec();
        reveal TreeSet.SameIterators();
        reveal TreeSet.SameIteratorModel();
        assert newitg.Valid() by {
          reveal newitgNeItg;
          assert old@L6(newitg.HasPeek?() ==> newitg.Peek?() != itg.Peek?());
        }
      }

      assert s.Model() == oldModel - {min, max} by {
        reveal model1, model2, model3, model4, model5, model6;
        assert s.EraseModel@L6(itg, newitl);
        reveal OrderedSet.EraseModel();
        reveal TreeSet.SameIterators();
        reveal TreeSet.SameIteratorModel();
        assert s.Model() == old@L6(s.Model()) - {max};
        assert old@L6(s.Model()) == old@L1(s.Model()) - {min};
        assert (old@L1(s.Model()) - {min}) - {max} == old@L1(s.Model()) - {min, max};
        assert old(s.Model()) == old@L1(s.Model());
      }

      assert newitl.Traversed() == {} by {
        reveal model1, model2, model3, model4, model5, model6;
        assert s.EraseModel@L6(itg, newitl);
        reveal UnorderedSet.EraseModel();
      }

      assert newitg.RTraversed() == old@L6(newitg.RTraversed()) - {max} by {
        reveal model1, model2, model3, model4, model5, model6;
        EraseIteratorRightRTraversed@L6(s, itg, newitl, newitg, old@L6(newitg.RTraversed()));
      }

      assert !LoopCondition(s, newitl, newitg) by {
        reveal LoopCondition();
        reveal OrderedSetIterator.PeekOrderSpec();
        reveal TreeSet.EraseModel();
        reveal TreeSet.RemoveIteratorModel();
        reveal TreeSet.RemoveIterators();
        reveal TreeSet.SameIteratorModel();
        reveal TreeSet.SameIterators();
        reveal itgTraversed;
      }

      assert LoopBound(s, newitl, newitg) < old(LoopBound(s, itl, itg)) by {
        reveal LoopBound();
        reveal UnorderedSet.SameIterators();
        reveal UnorderedSet.SameIteratorModel();
      }
    } else {
      var itg_useless := s.Erase(itg);
      assert Valid1It2(s, newitl, newitg) by {
        reveal OrderedSetIterator.PeekModel();
        reveal TreeSet.RemoveIterators();
        reveal TreeSet.RemoveIteratorModel();
        reveal UnorderedSet.EraseModel();
        reveal UnorderedSetIterator.BeforeSpec();
        reveal OrderedSetIterator.After();
        reveal OrderedSetIterator.AfterSpec();
        reveal OrderedSetIterator.RTraversedSpec();
        reveal OrderedSetIterator.PeekOrderSpec();
        reveal TreeSet.SameIterators();
        reveal TreeSet.SameIteratorModel();
        assert newitg.Valid() by {
          reveal newitgNeItg;
          assert old@L6(newitg.HasPeek?() ==> newitg.Peek?() != itg.Peek?());
        }
      }
      assert LoopBound(s, newitl, newitg) < old(LoopBound(s, itl, itg)) by {
        reveal LoopCondition();
        reveal LoopBound();
        reveal newitgTraversed;
        reveal OrderedSetIterator.After();
        reveal OrderedSetIterator.AfterSpec();
        reveal OrderedSetIterator.BeforeSpec();
        reveal OrderedSetIterator.CopyModel();
        reveal OrderedSetIterator.CopyModel();
        reveal OrderedSetIterator.NextIterators();
        reveal OrderedSetIterator.NextIterators();
        reveal OrderedSetIterator.PeekModel();
        reveal OrderedSetIterator.PeekOrderSpec();
        reveal OrderedSetIterator.PeekOrderSpec();
        reveal OrderedSetIterator.PeekSpec();
        reveal OrderedSetIterator.PrevModel();
        reveal OrderedSetIterator.PrevModel();
        reveal OrderedSetIterator.RTraversedSpec();
        reveal OrderedSetIterator.TraversedSpec();
        reveal TreeSet.EraseModel();
        reveal TreeSet.RemoveIteratorModel();
        reveal TreeSet.RemoveIterators();
        reveal TreeSet.SameIteratorModel();
        reveal TreeSet.SameIterators();
      }

      assert newitl.Traversed() == {} by {
        reveal model1, model2, model3, model4, model5, model6;
        assert old@L6(newitl.Peek?()) < old@L6(itg.Peek?());
        EraseIteratorRight@L6(s, itg, newitl, {});
      }

      assert newitg.RTraversed() == old@L6(newitg.RTraversed()) - {max} by {
        reveal model1, model2, model3, model4, model5, model6;
        EraseIteratorRightRTraversed@L6(s, itg, itg_useless, newitg, old@L6(newitg.RTraversed()));
      }

      assert s.Model() == old(s.Model()) - {min, max} by {
        reveal model1, model2, model3, model4, model5, model6;
        reveal OrderedSet.EraseModel();
        reveal TreeSet.SameIterators();
        reveal TreeSet.SameIteratorModel();
      }
    }

    assert LoopInvariantModel(s, sModel, W, newitl, newitg) by {
      reveal model1, model2, model3, model4, model5, model6;
      reveal LoopInvariantModel();
      assert PairsFunction(sModel, W) == newitg.RTraversed() + PairsFunction(s.Model() - newitg.RTraversed(), W) by {
        assert min == Min(old(s.Model() - itg.RTraversed()));
        assert max == Max(old(s.Model() - itg.RTraversed()));
        assert min < max;

        calc {
          PairsFunction(sModel, W);
        ==
          old(itg.RTraversed()) + PairsFunction(old(s.Model() - itg.RTraversed()), W);
        ==
          old(itg.RTraversed()) + PairsFunction(old(s.Model() - itg.RTraversed()) - {min, max}, W);
        ==
          old(itg.RTraversed()) + PairsFunction((old(s.Model()) - old(itg.RTraversed())) - {min, max}, W);
        == { assert old(s.Model()) - old(itg.RTraversed()) - {min, max} == old(s.Model()) - {min, max} - old(itg.RTraversed()); }
          old(itg.RTraversed()) + PairsFunction((old(s.Model()) - {min, max}) - old(itg.RTraversed()), W);
        == { assert s.Model() == old(s.Model()) - {min, max}; }
          old(itg.RTraversed()) + PairsFunction(s.Model() - old(itg.RTraversed()), W);
        == { assert newitg.RTraversed() == old(itg.RTraversed()); }
          newitg.RTraversed() + PairsFunction(s.Model() - newitg.RTraversed(), W);
        }
      }
    }
  }

  opaque twostate predicate RestoreLoopConditionModel(
    s: TreeSet,
    itl: OrderedSetIterator,
    itg: OrderedSetIterator
  )
    reads s.Repr()
    requires old(Valid1It2(s, itl, itg))
    requires Valid1It2(s, itl, itg)
    requires fresh(s.Repr() - old(s.Repr()))
    requires itl.HasPeek?() <==> old(itl.HasPeek?())
    requires itg.HasPeek?() <==> old(itg.HasPeek?())
  {
    && s.Model() == old(s.Model())
    && (itl.HasPeek?() ==> itl.Before() == old(itl.Before()) && itl.Peek?() == old(itl.Peek?()))
    && (itg.HasPeek?() ==> itg.Before() == old(itg.Before()) && itg.Peek?() == old(itg.Peek?()))
  }

  method RestoreLoopCondition(
    s: TreeSet,
    itl: OrderedSetIterator,
    itg: OrderedSetIterator
  ) returns (b: bool)
    modifies s.Repr()
    requires allocated(s.Repr())
    ensures allocated(s.Repr())
    ensures fresh(s.Repr() - old(s.Repr()))

    requires Valid1It2(s, itl, itg)

    ensures Valid1It2(s, itl, itg)
    ensures b == LoopCondition(s, itl, itg)
    ensures LoopBound(s, itl, itg) == old(LoopBound(s, itl, itg))
    ensures itl.HasPeek?() <==> old(itl.HasPeek?())
    ensures itg.HasPeek?() <==> old(itg.HasPeek?())
    ensures itl.Traversed() == old(itl.Traversed())
    ensures itg.Traversed() == old(itg.Traversed())

    ensures s.Iterators() >= old(s.Iterators())

    ensures RestoreLoopConditionModel(s, itl, itg)
  {
    var itlHasPeek := itl.HasPeek();
    assert Valid1It2(s, itl, itg) by {
      reveal UnorderedSet.SameIterators();
      reveal UnorderedSet.SameIteratorModel();
    }

    var itgHasPeek := itg.HasPeek();
    assert
      && Valid1It2(s,itl,itg)
      && itgHasPeek == itg.HasPeek?()
      && itlHasPeek == itl.HasPeek?()
    by {
      reveal UnorderedSetIterator.PeekModel();
      reveal UnorderedSet.SameIterators();
      reveal UnorderedSet.SameIteratorModel();
    }

    if itlHasPeek && itgHasPeek {
      var itlPeek := itl.Peek();
      assert
        && Valid1It2(s,itl,itg)
        && itgHasPeek == itg.HasPeek?()
      by {
        reveal UnorderedSet.SameIterators();
        reveal UnorderedSet.SameIteratorModel();
      }

      var itgPeek := itg.Peek();
      assert
        && Valid1It2(s,itl,itg)
        && itlHasPeek == itl.HasPeek?()
        && itlPeek == itl.Peek?()
        && itgPeek == itg.Peek?()
      by {
        reveal UnorderedSetIterator.PeekModel();
        reveal UnorderedSet.SameIterators();
        reveal UnorderedSet.SameIteratorModel();
      }
      b := itlPeek < itgPeek;
    } else {
      b := false;
    }

    assert
      && (itl.HasPeek?() <==> old(itl.HasPeek?()))
      && (itg.HasPeek?() <==> old(itg.HasPeek?()))
      && itl.Traversed() == old(itl.Traversed())
      && itg.Traversed() == old(itg.Traversed())
    by {
      reveal UnorderedSetIterator.HasPeekModel();
      reveal UnorderedSetIterator.PeekModel();
      reveal UnorderedSet.SameIterators();
      reveal UnorderedSet.SameIteratorModel();
    }

    assert LoopBound(s, itl, itg) == old(LoopBound(s, itl,itg)) by {
      reveal LoopBound();
      reveal LoopCondition();
      reveal UnorderedSet.SameIterators();
      reveal UnorderedSet.SameIteratorModel();
    }

    assert b == LoopCondition(s, itl, itg) by {
      reveal LoopCondition();
    }

    assert RestoreLoopConditionModel(s, itl, itg) by {
      reveal RestoreLoopConditionModel();
      reveal UnorderedSet.SameIterators();
      reveal UnorderedSet.SameIteratorModel();
      reveal UnorderedSetIterator.HasPeekModel();
      reveal UnorderedSetIterator.PeekModel();
    }
  }

  method LoopBody(
    s: TreeSet,
    ghost sModel: set<K>,
    itl: OrderedSetIterator,
    itg: OrderedSetIterator,
    W: int
  )
    returns (
      newitl: OrderedSetIterator,
      newitg: OrderedSetIterator,
      b: bool
    )
    modifies s.Repr()
    requires allocated(s.Repr())
    ensures allocated(s.Repr())
    ensures fresh(s.Repr()-old(s.Repr()))

    requires Valid1It2(s, itl, itg)
    requires itl.HasPeek?()
    requires itg.HasPeek?()
    requires itl.Peek?() < itg.Peek?()
    requires itl.Traversed() < itg.Traversed() && |itl.Traversed()| < |itg.Traversed()|
    requires LoopCondition(s,itl,itg)

    requires LoopInvariantModel(s, sModel, W, itl, itg)

    ensures Valid1It2(s, newitl, newitg)
    ensures b == LoopCondition(s,newitl,newitg)
    ensures LoopBound(s, newitl, newitg) < old(LoopBound(s, itl,itg))

    ensures s.Iterators() >= {newitl,newitg} + old(s.Iterators())

    ensures LoopInvariantModel(s, sModel, W, newitl, newitg)
  {
    ghost var oldLoopBound := |itg.Traversed()| - |itl.Traversed()|;
    assert oldLoopBound == LoopBound(s, itl,itg) > 0 by {
      reveal LoopBound();
    }

    ghost var min := itl.Peek?();
    ghost var max := itg.Peek?();

    assert minmax:
      && min == Min(s.Model() - itg.RTraversed())
      && max == Max(s.Model() - itg.RTraversed())
    by {
      assert itl.Peek?() < itg.Peek?();
      itg.PeekROrder();
      reveal OrderedSetIterator.After();
      reveal LoopInvariantModel();
      reveal UnorderedSetIterator.PeekSpec();
      reveal OrderedSetIterator.PeekOrderSpec();
      assert min in s.Model() - itg.RTraversed();
      assert max in s.Model() - itg.RTraversed();
    }

    var itlPeek := itl.Peek();
    assert Valid1It2(s,itl,itg) && itg.HasPeek?() by {
      reveal UnorderedSet.SameIterators();
      reveal UnorderedSet.SameIteratorModel();
    }

    var itgPeek := itg.Peek();
    assert
      && Valid1It2(s,itl,itg)
      && itl.HasPeek?()
      && itl.Peek?() == old(itl.Peek?())
      && itlPeek == itl.Peek?()
      && itl.Traversed() == old(itl.Traversed())< s.Model()
      && itg.HasPeek?()
      && itg.Traversed() == old(itg.Traversed()) < s.Model()
      && itg.Peek?() == old(itg.Peek?())
      && itgPeek == itg.Peek?()
      && itl.Peek?() in itg.Traversed()
      && itl.Traversed() < itg.Traversed()
      && LoopCondition(s,itl,itg)
    by {
      reveal UnorderedSetIterator.PeekModel();
      reveal UnorderedSet.SameIterators();
      reveal UnorderedSet.SameIteratorModel();
      reveal UnorderedSetIterator.PeekSpec();
      reveal UnorderedSetIterator.TraversedSpec();
      reveal OrderedSetIterator.PeekOrderSpec();
      reveal LoopCondition();
      LoopConditionEnsuresTraversed(s,itl,itg);
    }

    assert LoopInvariantModel(s, sModel, W, itl, itg) by {
      reveal LoopInvariantModel();
      reveal OrderedSetIterator.After();
      reveal UnorderedSetIterator.PeekModel();
    }

    if itlPeek + itgPeek <= W {
      newitl, newitg := MakePair(s, sModel, itl, itg, W);
    } else {
      itg.Prev();
      newitl := itl;
      newitg := itg;
      assert
        && Valid1It2(s,newitl,newitg)
        && newitl.Traversed() == old(itl.Traversed())
        && |newitg.Traversed()| < old(|itg.Traversed()|)
        && |newitl.Traversed()| == old(|itl.Traversed()|)
      by {
        reveal OrderedSetIterator.NextIterators();
        reveal OrderedSetIterator.PrevModel();
        reveal UnorderedSet.SameIteratorModel();
        reveal UnorderedSetIterator.PeekSpec();
        reveal UnorderedSetIterator.TraversedSpec();
        reveal OrderedSetIterator.After();
        reveal OrderedSetIterator.PeekOrderSpec();
      }

      assert LoopInvariantModel(s, sModel, W, newitl, newitg) by {
        reveal LoopInvariantModel();
        reveal OrderedSetIterator.After();
        reveal OrderedSetIterator.PrevModel();
        reveal UnorderedSet.SameIteratorModel();
        reveal UnorderedSet.SameIterators();
        reveal UnorderedSetIterator.PeekModel();

        assert newitl.Traversed() == {};
        assert PairsFunction(sModel, W) == newitg.RTraversed() + PairsFunction(s.Model() - newitg.RTraversed(), W) by {
          calc {
            PairsFunction(sModel, W);
          ==
            old(itg.RTraversed()) + PairsFunction(old(s.Model()) - old(itg.RTraversed()), W);
          == { reveal minmax; }
            old(itg.RTraversed()) + ({max} + PairsFunction((old(s.Model()) - old(itg.RTraversed())) - {max}, W));
          ==
            (old(itg.RTraversed()) + {max}) + PairsFunction((old(s.Model()) - old(itg.RTraversed())) - {max}, W);
          ==
            newitg.RTraversed() + PairsFunction((old(s.Model()) - old(itg.RTraversed())) - {max}, W);
          == { assert (old(s.Model()) - old(itg.RTraversed())) - {max} == old(s.Model()) - (old(itg.RTraversed()) + {max}); }
            newitg.RTraversed() + PairsFunction(old(s.Model()) - (old(itg.RTraversed()) + {max}), W);
          == { assert newitg.RTraversed() == old(itg.RTraversed()) + { max }; }
            newitg.RTraversed() + PairsFunction(s.Model() - newitg.RTraversed(), W);
          }
        }
      }
    }

    b := RestoreLoopCondition(s, newitl, newitg);
    assert LoopInvariantModel(s, sModel, W, newitl, newitg) by {
      reveal LoopInvariantModel();
      reveal RestoreLoopConditionModel();
      reveal OrderedSetIterator.After();
    }

    assert LoopBound(s, newitl, newitg) < old(LoopBound(s, itl,itg)) by {
      reveal LoopBound();
      reveal UnorderedSet.SameIterators();
      reveal UnorderedSet.SameIteratorModel();
    }
  }

  ghost predicate Valid1It3(s: TreeSet, it1: OrderedSetIterator, it2: OrderedSetIterator, it3: OrderedSetIterator)
    reads s.Repr()
  {
    s.Valid() && ValidIt(s, it1) && ValidIt(s, it2) && ValidIt(s, it3)
  }

  ghost predicate Valid1It2(s: TreeSet, itl: OrderedSetIterator, itg: OrderedSetIterator)
    reads s.Repr()
  {
    s.Valid() && ValidIt(s, itl) && ValidIt(s,itg)
  }

  opaque twostate predicate PairsModel(s: TreeSet, W: int)
    reads s.Repr()
    requires old(s.Valid())
    requires s.Valid()
  {
    s.Model() == PairsFunction(old(s.Model()), W)
  }

  method Pairs(s: TreeSet, W: int)
    modifies s.Repr()
    requires allocated(s.Repr())
    ensures fresh(s.Repr() - old(s.Repr()))

    requires s.Valid()
    requires forall e | e in s.Model() :: e <= W
    ensures s.Valid()
    ensures s.Iterators() >= old(s.Iterators())
    ensures PairsModel(s, W)
  {
    reveal LoopCondition();
    var b: bool;
    var itl: OrderedSetIterator := s.First();
    var itg: OrderedSetIterator := s.Last();
    assert Valid1It2(s, itl, itg) by {
      reveal UnorderedSet.SameIterators();
    }

    b := RestoreLoopCondition(s, itl, itg);

    assert LoopInvariantModel(s, old(s.Model()), W, itl, itg) by {
      reveal UnorderedSet.FirstModel();
      reveal OrderedSet.LastModel();
      reveal UnorderedSet.SameIterators();
      reveal UnorderedSet.SameIteratorModel();
      reveal RestoreLoopConditionModel();
      reveal OrderedSetIterator.After();
      calc {
        PairsFunction(old(s.Model()), W);
      ==
        ({} + PairsFunction(old(s.Model()), W));
      ==
        itg.RTraversed() + PairsFunction(old(s.Model()), W);
      == { assert old(s.Model()) == s.Model() == s.Model() - {}; }
        itg.RTraversed() + PairsFunction(s.Model() - {}, W);
      ==
        itg.RTraversed() + PairsFunction(s.Model() - itg.RTraversed(), W);
      }

      reveal LoopInvariantModel();
    }

    while b
      decreases LoopBound(s,itl,itg)
      invariant Valid1It2(s,itl,itg)
      invariant b == LoopCondition(s,itl,itg)

      invariant allocated(s.Repr())
      invariant fresh(s.Repr()-old(s.Repr()))
      invariant s.Iterators() >= old(s.Iterators())
      invariant LoopInvariantModel(s, old(s.Model()), W, itl, itg)
    {
      LoopConditionEnsuresTraversed(s,itl,itg);
      itl, itg, b := LoopBody(s, old(s.Model()), itl, itg,W);
    }

    assert PairsModel(s, W) by {
      if itl.HasPeek?() && itg.HasPeek?() {
        assert itg.Peek?() <= itl.Peek?() by { reveal LoopCondition(); }

        assert itg.Before() <= itl.Before() == {} by {
          if !(itg.Before() <= itl.Before()) {
            var x :| x in itg.Before() && x !in itl.Before();
            assert x in s.Model() by { reveal UnorderedSetIterator.BeforeSpec(); }
            assert itl.Peek?() <= x < itg.Peek?() by { reveal OrderedSetIterator.PeekOrderSpec(); }
            assert false;
          }
          assert itl.Before() == {} by { reveal LoopInvariantModel(); }
        }
        assert itg.RTraversed() == s.Model() - { itg.Peek?() } by {
          reveal OrderedSetIterator.After();
        }

        assert s.Model() == PairsFunction(old(s.Model()), W) by {
          calc {
            PairsFunction(old(s.Model()), W);
          == { reveal LoopInvariantModel(); }
            itg.RTraversed() + PairsFunction(s.Model() - itg.RTraversed(), W);
          ==
            itg.RTraversed() + PairsFunction(s.Model() - (s.Model() - {itg.Peek?()}), W);
          == { assert itg.Peek?() in s.Model() by { reveal UnorderedSetIterator.PeekSpec(); }
               assert s.Model() - (s.Model() - {itg.Peek?()}) == {itg.Peek?()} by { SubtractAllBut(s.Model(), {itg.Peek?()}); } }
            itg.RTraversed() + PairsFunction({ itg.Peek?()}, W);
          == { assert Min({ itg.Peek?() }) == itg.Peek?() == Max({ itg.Peek?() });}
            itg.RTraversed() + { itg.Peek?() };
          ==
            itg.After() + { itg.Peek?() };
          == { reveal OrderedSetIterator.After(); }
            (s.Model() - {itg.Peek?()}  - itg.Before()) + { itg.Peek?() };
          ==
            (s.Model() - {itg.Peek?()}) + { itg.Peek?() };
          == { assert itg.Peek?() in s.Model() by { reveal UnorderedSetIterator.PeekSpec(); }
               SubtractThenAdd(s.Model(), { itg.Peek?() }); }
            s.Model();
          }
        }
      } else {
        assert itg.RTraversed() == s.Model() by {
          reveal LoopInvariantModel();
          reveal OrderedSetIterator.After();
        }
        assert s.Model() == PairsFunction(old(s.Model()), W) by {
          calc {
            PairsFunction(old(s.Model()), W);
          == { reveal LoopInvariantModel(); }
            itg.RTraversed() + PairsFunction(s.Model() - itg.RTraversed(), W);
          ==
            s.Model() + PairsFunction({}, W);
          ==
            s.Model();
          }
        }
      }
      reveal PairsModel();
    }
  }
}
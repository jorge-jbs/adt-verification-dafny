include "../../src/Collections/SetInt.dfy"
include "../../src/TreeSet/TreeSetSpec.dfy"
include "../../src/OrderedSet/OrderedSetSpec.dfy"

module RemoveHalves {
  import opened KeyValue
  import opened SetInt
  import opened ADT
  import opened TreeSetSpec
  import opened OrderedSetSpec

  opaque ghost function LoopBound(s: TreeSet, it: OrderedSetIterator): nat
    reads s.Repr()
    requires Valid1It1(s, it)
  {
    reveal it.TraversedSpec();
    |s.Model()| - |it.Traversed()|
  }

  opaque ghost predicate LoopInvariant(s: TreeSet, it: OrderedSetIterator, oldModel: set<int>)
    reads s.Repr()
    requires Valid1It1(s, it)
  {
    && (forall x <- s.Model() :: x >= 0)
    && s.Model() <= oldModel
    && (it.HasPeek?() ==> forall x | it.Peek?() < x :: x in oldModel <==> x in s.Model())
    && s.Model() == oldModel - (set x <- oldModel | (it.HasPeek?() ==> x < it.Peek?()) && x % 2 == 0 :: x/2)
  }

  method LoopBody(s: TreeSet, it: OrderedSetIterator, ghost oldModel: set<int>)
    returns (hasPeek: bool)
    modifies s.Repr()
    requires allocated(s.Repr())
    ensures allocated(s.Repr())
    ensures Fresh(s)

    requires Valid1It1(s, it)
    requires it.HasPeek?()
    requires LoopInvariant(s, it, oldModel)
    ensures Valid1It1(s, it)
    ensures hasPeek == it.HasPeek?()
    ensures LoopBound(s, it) < old(LoopBound(s, it))
    ensures LoopInvariant(s, it, oldModel)
    ensures s.Iterators() >= old(s.Iterators())
  {
    var x := it.Peek();
    assert forall n: int | n == n / 2 :: n == -1 || n == 0;
    if x == 0 {
      it.Next();
      label PreRemove:
      assert s.RemoveIteratorModelPre(it, x/2) by {
        reveal s.RemoveIteratorModelPre();
        reveal it.NextModel(), it.PeekModel(), it.PeekSpec(), it.PeekOrderSpec();
      }
      assert x == x/2;
      s.Remove(x);
      s.RemoveIterator@PreRemove(it, x/2);
      assert LoopBound(s, it) < old(LoopBound(s, it)) by {
        reveal LoopBound();
        reveal it.PeekModel();
        reveal it.PeekSpec();
        reveal it.NextModel();
        reveal s.RemoveModel();
        reveal s.RemoveIteratorModel();
        assert old@PreRemove(it.HasPeek?() ==> x/2 < it.Peek?()) by {
          reveal it.PeekOrderSpec();
        }
        calc {
          |s.Model()| - |it.Traversed()|;
          == (old(|s.Model()| - 1)) - |it.Traversed()|;
          == (old(|s.Model()| - 1)) - old@PreRemove(|it.Traversed()|-1);
          == (old(|s.Model()| - 1)) - old(|it.Traversed()|);
          < old(|s.Model()| - |it.Traversed()|);
        }
      }
      assert LoopInvariant(s, it, oldModel) by {
        reveal LoopInvariant();
        reveal it.PeekModel();
        reveal it.PeekSpec();
        reveal it.PeekOrderSpec();
        reveal it.NextModel();
        reveal s.RemoveModel();
        reveal s.RemoveIteratorModel();
      }
    } else {
      label PreRemove:
      if x % 2 == 0 {
        assert s.RemoveIteratorModelPre(it, x/2) by {
          reveal s.RemoveIteratorModelPre();
          reveal it.NextModel(), it.PeekModel(), it.PeekSpec();
        }
        s.Remove(x/2);
        s.RemoveIterator@PreRemove(it, x/2);
      }
      assert it.HasPeek?() by {
        reveal s.RemoveIteratorModel();
      }
      label PreNext:
      it.Next();
      assert LoopBound(s, it) < old(LoopBound(s, it)) by {
        reveal LoopBound();
        reveal it.PeekModel();
        reveal it.PeekSpec();
        reveal it.NextModel();
        reveal s.RemoveModel();
        reveal s.RemoveIteratorModel();
      }
      assert LoopInvariant(s, it, oldModel) by {
        reveal LoopInvariant();
        reveal RemoveHalvesModelPre();
        reveal it.PeekModel();
        reveal it.PeekSpec();
        reveal it.PeekOrderSpec();
        reveal it.TraversedSpec();
        reveal it.NextModel();
        reveal s.RemoveModel();
        reveal s.RemoveIteratorModel();
      }
    }
    hasPeek := it.HasPeek();
    assert LoopBound(s, it) < old(LoopBound(s, it)) by {
      reveal LoopBound();
      reveal it.HasPeekModel();
    }
    assert LoopInvariant(s, it, oldModel) by {
      reveal LoopInvariant();
      reveal it.HasPeekModel();
    }
  }

  opaque ghost predicate RemoveHalvesModelPre(s: TreeSet)
    reads s.Repr()
    requires s.Valid()
  {
    forall x <- s.Model() :: x >= 0
  }

  opaque twostate predicate RemoveHalvesModel(s: TreeSet)
    reads s.Repr()
    requires old(s.Valid())
    requires s.Valid()
  {
    s.Model() == set x <- old(s.Model()) | x*2 !in old(s.Model())
  }

  method RemoveHalves(s: TreeSet)
    modifies s.Repr()
    requires allocated(s.Repr())
    ensures allocated(s.Repr())
    ensures Fresh(s)

    requires s.Valid()
    requires RemoveHalvesModelPre(s)
    ensures s.Valid()
    ensures RemoveHalvesModel(s)

    ensures s.Iterators() >= old(s.Iterators())
  {
    var it: OrderedSetIterator := s.First();
    var hp := it.HasPeek();

    assert LoopInvariant(s, it, old(s.Model())) by {
      reveal LoopInvariant(), RemoveHalvesModelPre(), s.FirstModel(), it.HasPeekModel(), it.PeekOrderSpec();
    }
    while hp
      decreases LoopBound(s, it)
      invariant allocated(s.Repr())
      invariant Fresh(s)
      invariant Valid1It1(s, it)
      invariant s.Iterators() >= old(s.Iterators())
      invariant hp == it.HasPeek?()
      invariant LoopInvariant(s, it, old(s.Model()))
    {
      hp := LoopBody(s, it, old(s.Model()));
    }

    assert RemoveHalvesModel(s) by {
      reveal RemoveHalvesModel(), LoopInvariant();
    }
  }
}

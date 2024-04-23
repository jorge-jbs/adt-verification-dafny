include "../../src/TreeSet/TreeSetSpec.dfy"
include "../../src/OrderedSet/OrderedSetSpec.dfy"

module RemoveHalvesNoModel {
  import opened KeyValue
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

  method LoopBody(s: TreeSet, it: OrderedSetIterator)
    returns (hasPeek: bool)
    modifies s.Repr()
    requires allocated(s.Repr())
    ensures allocated(s.Repr())
    ensures Fresh(s)

    requires Valid1It1(s, it)
    requires it.HasPeek?()
    ensures Valid1It1(s, it)
    ensures hasPeek == it.HasPeek?()
    ensures LoopBound(s, it) < old(LoopBound(s, it))
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
    } else {
      if x % 2 == 0 {
        label PreRemove:
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
      it.Next();
      assert LoopBound(s, it) < old(LoopBound(s, it)) by {
        reveal LoopBound();
        reveal it.PeekModel();
        reveal it.PeekSpec();
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
  }

  method RemoveHalves(s: TreeSet)
    modifies s.Repr()
    requires allocated(s.Repr())
    ensures allocated(s.Repr())
    ensures Fresh(s)

    requires s.Valid()
    ensures s.Valid()

    ensures s.Iterators() >= old(s.Iterators())
  {
    var it: OrderedSetIterator := s.First();
    var hp := it.HasPeek();
    while hp
      decreases LoopBound(s, it)
      invariant allocated(s.Repr())
      invariant Fresh(s)
      invariant Valid1It1(s, it)
      invariant s.Iterators() >= old(s.Iterators())
      invariant hp == it.HasPeek?()
    {
      hp := LoopBody(s, it);
    }
  }
}

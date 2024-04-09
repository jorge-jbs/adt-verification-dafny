include "../../src/TreeSet/TreeSetSpec.dfy"
include "../../src/OrderedSet/OrderedSetSpec.dfy"

module RemoveDoubles {
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

  lemma Prueba()
  {
    assert -1 / 2 * 2 == -2;
    assert 1 / 2 * 2 == 0;
    assert 5 / 2 * 2 == 4;
    assert !forall n: int :: n == n / 2 * 2;
    assert forall n: int | n % 2 == 0 :: n == n / 2 * 2;
    assert forall s: set<int> ::
      (set x <- s | x*2 !in s) == s - (set x <- s | x % 2 == 0 :: x/2);
    assert -1 % 2 == 1;
    assert 0 % 2 == 0;

/*
    assert forall n: int, k: int | k >= 2 && n % k == 0 :: n == n / k * k;
    assert forall s: set<int>, k: int | k >= 2 ::
      (set x <- s | x*k !in s) == s - (set x <- s | x % k == 0 :: x/k)
    by {
      forall x: int, s: set<int>, k: int | k >= 2
        ensures
          x in (set x <- s | x*k !in s)
          <==> x in (s - (set x <- s | x % k == 0 :: x/k))
      {
        if x in (set x <- s | x*k !in s) {
          assert x in (s - (set x <- s | x % k == 0 :: x/k));
        }
        if x in (s - (set x <- s | x % k == 0 :: x/k)) {
          assert x in s;
          assert x !in (set n <- s | n % k == 0 :: n/k);
          assert forall n <- s :: n % k != 0 || n/k != x;
          assert forall n <- s | n % k == 0 :: n/k != x;
          assert forall n <- s | n % k == 0 :: n/k*k != x*k;
          assert forall n <- s | n % k == 0 :: n != x*k;
          assume false;
          assert forall n <- s | n % k != 0 :: n != x*k;
          assert forall n <- s :: n != x*k;
          assert x in (set x <- s | x*k !in s);
        }
      }
    }
    */
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
    /*
    There are two cases:

    1) x == x/2
    2) x != x/2

    The first case is only when x ∊ {-1, 0}:
    */
    assert forall n: int | n == n / 2 :: n == -1 || n == 0;
    if x == -1 || x == 0 {
      /*
      In this case I cannot remove `x/2` directly, since that would invalidate `it`.
      First, I advance `it` and then I remove `x/2`.
      */
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
      /*
      You may wonder why I do not merge both cases. It is because
      a set can have `x` and `x/2` and not any other element in between.
      If I advance `it` before removing `x/2`, and (x < 0), then I
      `it.Peek?() == x/2` and I would invalidate `it` after removing `x/2`.
      */
      label PreRemove:
      assert s.RemoveIteratorModelPre(it, x/2) by {
        reveal s.RemoveIteratorModelPre();
        reveal it.NextModel(), it.PeekModel(), it.PeekSpec();
      }
      s.Remove(x/2);
      s.RemoveIterator@PreRemove(it, x/2);
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

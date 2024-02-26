include "../../src/ADT.dfy"
include "../../src/Collections/KeyValue.dfy"
include "../../src/Collections/SetInt.dfy"

module OrdSetContainedOpaquePrimePrime {
  import opened ADT
  import opened KeyValue
  import opened SetInt

  trait OrderedSetIterator {
    ghost function Parent(): OrderedSet
      reads this

    ghost predicate Valid()
      reads this, Parent(), Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()

    ghost predicate HasPeek?()
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      //ensures HasPeek?() ==> Traversed() < Parent().Model() &&  |Traversed()| < |Parent().Model()|
      //ensures !HasPeek?() ==> Traversed() == Parent().Model() && |Traversed()| == |Parent().Model()|

/*
    lemma BeforeStrictSubsetOfHasPeek()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Before'() < Parent().Model()
      //ensures |Before'()| < |Parent().Model()|

    lemma HasPeekOfBeforeStrictSubset()
      requires Valid()
      requires Parent().Valid()
      requires Before'() < Parent().Model()
      //requires |Before'()| < |Parent().Model()|
      ensures HasPeek?()
      */

    ghost predicate PastTheEnd?()
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires !HasPeek?()

    ghost predicate PastTheBeginning?()
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires !HasPeek?()
    {
      !PastTheEnd?()
    }

    opaque ghost predicate BeforeSpec(before: set<K>)
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
    {
      && before < Parent().Model()
      && |before| < |Parent().Model()|
    }

    ghost function Before(): set<K>
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures BeforeSpec(Before())

    opaque ghost predicate Before'Spec(before': set<K>)
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
    {
      && before' <= Parent().Model()
      && 0 <= |before'| <= |Parent().Model()|
    }

    ghost function Before'(): set<K>
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures Before'Spec(Before'())
      //ensures Before'() <= Parent().Model()
    {
      if HasPeek?() then
        assert Before'Spec(Before()) by { reveal BeforeSpec(), Before'Spec(); }
        Before()
      else if PastTheEnd?() then
        assert Before'Spec(Parent().Model()) by { reveal BeforeSpec(), Before'Spec(); }
        Parent().Model()
      else
        assert Before'Spec({}) by { reveal BeforeSpec(), Before'Spec(); }
        {}
    }

/*
    lemma Before'InModel()
      requires Valid()
      requires Parent().Valid()
      ensures Before'() <= Parent().Model()
      ensures 0 <= |Before'()| <= |Parent().Model()|
      */

    ghost function After(): set<K>
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
    {
      (Parent().Model() - Before'()) - {Peek?()}
    }

    ghost function After'(): set<K>
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
    {
      if HasPeek?() then
        After()
      else if PastTheBeginning?() then
        {}
      else
        Parent().Model()
    }

    lemma PeekGtBefore(x: K)
      requires Valid()
      requires HasPeek?()
      requires x in Before()
      ensures x < Peek?()

    lemma PeekLtAfter(x: K)
      requires Valid()
      requires HasPeek?()
      requires x in After()
      ensures Peek?() < x

    opaque ghost predicate PeekSpec(p: K)
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
    {
      && p in Parent().Model()
      && p !in Before()
      //&& (forall x <- Before() :: x < p)
      //&& assert p in Parent().Model() - Before();
      //&& assert Parent().Model() - Before() != {};
      //&& p == Min(Parent().Model()-Before())
    }

    ghost function Peek?(): K
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures PeekSpec(Peek?())

    opaque twostate predicate HasPeekModel()
      reads this, Parent(), Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
      requires old(HasPeek?()) ==> HasPeek?()
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && Before'() == old(Before'())
      && |Before'()| == old(|Before'()|)
      && (old(HasPeek?()) ==> Peek?() == old(Peek?()))
    }

    method HasPeek() returns (b: bool)
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures old(HasPeek?()) ==> HasPeek?()
      //ensures !old(HasPeek?()) ==> !HasPeek?()
      ensures b == HasPeek?()
      ensures Parent().Iterators() >= old(Parent().Iterators())

      ensures HasPeekModel()
      /*
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))
      */

    opaque twostate predicate NextModel()
      reads this, Parent(), Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
      requires old(HasPeek?())
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && Before'() == {old(Peek?())} + old(Before())
      && |Before'()| == 1 + old(|Before()|)
    }

    method Next()
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      //ensures Parent().Model() == old(Parent().Model())
      //ensures |Parent().Model()| == old(|Parent().Model()|)

      //ensures Traversed() == {old(Peek?())} + old(Traversed())
      //ensures |Traversed()| == 1 + old(|Traversed()|)

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures NextModel()
      /*
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && (it != this ==> it.Traversed() == old(it.Traversed())
                                   && |it.Traversed()| == old(|it.Traversed()|)
                                   && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?())))
      */

    opaque twostate predicate PeekModel()
      reads this, Parent(), Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
      requires old(HasPeek?())
      requires HasPeek?()
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && Before'() == old(Before'())
      && |Before'()| == old(|Before'()|)
      && Peek?() == old(Peek?())
    }

    method Peek() returns (p: K)
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures HasPeek?()
      ensures p == Peek?()
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures PeekModel()
      /*
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))
                */
  }

  trait OrderedSet extends ADT<set<K>> {
    ghost function Iterators(): set<OrderedSetIterator>
      reads this, Repr()
      requires Valid()
      ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
  }

  ghost predicate SCInv(s1: OrderedSet, s2: OrderedSet)
    reads s1, s1.Repr(), s2, s2.Repr()
  {
    && s1.Valid() && s2.Valid()
    && {s1} + s1.Repr() !! {s2} + s2.Repr()
  }

  twostate predicate DCInv(s1: OrderedSet, s2: OrderedSet)
    reads s1, s1.Repr(), s2, s2.Repr()
    requires old(SCInv(s1, s2))
    requires SCInv(s1, s2)
  {
    && fresh(s1.Repr() - old(s1.Repr()))
    && fresh(s2.Repr() - old(s2.Repr()))
    && s1.Iterators() >= old(s1.Iterators())
    && s2.Iterators() >= old(s2.Iterators())
  }

  opaque twostate predicate DFInv(s1: OrderedSet, s2: OrderedSet)
    reads s1, s1.Repr(), s2, s2.Repr()
    requires old(SCInv(s1, s2))
    requires SCInv(s1, s2)
  {
    && s1.Model() == old(s1.Model())
    && s2.Model() == old(s2.Model())
  }

  ghost predicate LoopSCInv(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      it1HasPeek: bool,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      it2HasPeek: bool,
      b: bool
    )
    reads s1, s1.Repr(), s2, s2.Repr(), it1, it2
  {
    && SCInv(s1, s2)

    && it1.Parent() == s1
    && it2.Parent() == s2
    && it1.Valid()
    && it2.Valid()
    && it1 in s1.Iterators()
    && it2 in s2.Iterators()
    && it1HasPeek == it1.HasPeek?()
    && it2HasPeek == it2.HasPeek?()
  }

  opaque ghost predicate LoopSFInv(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      it1HasPeek: bool,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      it2HasPeek: bool,
      b: bool
    )
    reads s1, s1.Repr(), s2, s2.Repr(), it1, it2
    requires LoopSCInv(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
  {
    && (b ==> it1.Before'() <= it2.Before'())
    && (!b ==> !(it1.Before'() <= s2.Model()))
    && (it1.HasPeek?() ==>
      && it1.Peek?() !in it2.Before'()
      && (forall u <- it2.Before'() :: u < it1.Peek?())
    )
  }

  opaque ghost function LoopTermination(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      it1HasPeek: bool,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      it2HasPeek: bool,
      b: bool
    ): int
    reads s1, s1.Repr(), s2, s2.Repr(), it1, it2
    requires LoopSCInv(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
  {
    |s2.Model()| - |it2.Before'()| + (if b then 1 else 0)
  }

  // 2.16M RU (~2.6s) - correctness verification
  // 4.14M RU (~3.9s) - correctness and functional verification
  // 11.1M RU (~9.2s) - correctness and functional verification (reveal all at the end)
  // 8.05M RU (~6.9s) - correctness verification (reveal all at the end)
  // 6.77M RU (~5.7s) - correctness verification and termination (reveal all at the end)
  // 11.3M RU (~8.9s) - correctness and functional verification (nothing is opaque)
  method Loop1(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      it1HasPeek: bool,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      it2HasPeek: bool,
      b: bool
    )
    returns (
      newIt1HasPeek: bool,
      newIt2HasPeek: bool,
      newB: bool
    )
    modifies s1, s1.Repr(), s2, s2.Repr()
    ensures fresh(s1.Repr() - old(s1.Repr()))
    ensures fresh(s2.Repr() - old(s2.Repr()))
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())
    requires it1HasPeek && it2HasPeek && b
    requires LoopSCInv(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
    requires LoopSFInv(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
    ensures LoopSCInv(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
    ensures LoopSFInv(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
    ensures DCInv(s1, s2)
    ensures DFInv(s1, s2)
    ensures 0 <= LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))

    requires it1.Peek?() == it2.Peek?()
  {
    it1.Next();
    newIt1HasPeek := it1.HasPeek();
    it2.Next();
    newIt2HasPeek := it2.HasPeek();
    newB := b;
    assert
      && DFInv(s1, s2)
    by {
      //assume false;
      reveal DFInv();
      reveal it1.NextModel(), it1.HasPeekModel();
      reveal it2.NextModel(), it2.HasPeekModel();
    }
    assert
      && LoopSFInv(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      && 0 <= LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
        < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))
    by {
      //assume false;
      reveal DFInv(), LoopSFInv(), LoopTermination();
      reveal it1.PeekSpec(), it1.BeforeSpec(), it1.Before'Spec(), it1.NextModel(), it1.HasPeekModel();
      reveal it2.PeekSpec(), it2.BeforeSpec(), it2.Before'Spec(), it2.NextModel(), it2.HasPeekModel();
      assert it1.Before'() <= it2.Before'();
      if it1.HasPeek?() {
        assert it1.Peek?() !in it2.Before'() by {
          assert old(it1.Peek?()) !in old(it2.Before'());
          assert old(it1.Peek?()) !in old(it1.Before'());
          assert it1.Peek?() !in it1.Before'();
          assert it2.Before'() == {old(it1.Peek?())} + old(it2.Before'());
          assert it1.Before'() == {old(it1.Peek?())} + old(it1.Before'());
        }
        assert (forall u <- it2.Before'() :: u < it1.Peek?());
      }
    }
    /*
    reveal DFInv();
    reveal it1.NextModel(), it1.HasPeekModel();
    reveal it2.NextModel(), it2.HasPeekModel();
    reveal DFInv(), LoopSFInv(), LoopTermination();
    reveal it1.PeekSpec(), it1.BeforeSpec(), it1.Before'Spec(), it1.NextModel(), it1.HasPeekModel();
    reveal it2.PeekSpec(), it2.BeforeSpec(), it2.Before'Spec(), it2.NextModel(), it2.HasPeekModel();
    */
  }

  // 17.9M RU (~15.1s) - correctness verification
  method Loop(
      s1: OrderedSet,
      it1: OrderedSetIterator,
      it1HasPeek: bool,
      s2: OrderedSet,
      it2: OrderedSetIterator,
      it2HasPeek: bool,
      b: bool
    )
    returns (
      newIt1HasPeek: bool,
      newIt2HasPeek: bool,
      newB: bool
    )
    modifies s1, s1.Repr(), s2, s2.Repr()
    ensures fresh(s1.Repr() - old(s1.Repr()))
    ensures fresh(s2.Repr() - old(s2.Repr()))
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())
    requires it1HasPeek && it2HasPeek && b
    requires LoopSCInv(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
    requires LoopSFInv(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b)
    ensures LoopSCInv(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
    ensures LoopSFInv(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
    ensures DCInv(s1, s2)
    ensures DFInv(s1, s2)
    ensures 0 <= LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))
  {
    var it1Peek := it1.Peek();
    var it2Peek := it2.Peek();
    if it1Peek == it2Peek {
      it1.Next();
      newIt1HasPeek := it1.HasPeek();
      it2.Next();
      newIt2HasPeek := it2.HasPeek();
      newB := b;
      assert (newB ==> it1.Before'() <= it2.Before'()) by {
        reveal DFInv(), LoopSFInv(), LoopTermination();
        reveal it1.PeekSpec(), it1.BeforeSpec(), it1.Before'Spec(), it1.PeekModel(), it1.NextModel(), it1.HasPeekModel();
        reveal it2.PeekSpec(), it2.BeforeSpec(), it2.Before'Spec(), it2.PeekModel(), it2.NextModel(), it2.HasPeekModel();
      }
    } else if it1Peek < it2Peek {
      newB := false;
      it1.Next();
      newIt1HasPeek := it1.HasPeek();
      newIt2HasPeek := it2.HasPeek();
      assert (newB ==> it1.Before'() <= it2.Before'()) by {
        reveal DFInv(), LoopSFInv(), LoopTermination();
        reveal it1.PeekSpec(), it1.BeforeSpec(), it1.Before'Spec(), it1.PeekModel(), it1.NextModel(), it1.HasPeekModel();
        reveal it2.PeekSpec(), it2.BeforeSpec(), it2.Before'Spec(), it2.PeekModel(), it2.NextModel(), it2.HasPeekModel();
      }
      assert {:only} (!newB ==> !(it1.Before'() <= s2.Model())) by {
        reveal it1.PeekSpec(), it1.BeforeSpec(), it1.Before'Spec(), it1.PeekModel(), it1.NextModel(), it1.HasPeekModel();
        reveal it2.PeekSpec(), it2.BeforeSpec(), it2.Before'Spec(), it2.PeekModel(), it2.NextModel(), it2.HasPeekModel();
        assume false;
        reveal DFInv(), LoopSFInv(), LoopTermination();
        reveal it1.PeekSpec(), it1.BeforeSpec(), it1.Before'Spec(), it1.PeekModel(), it1.NextModel(), it1.HasPeekModel();
        reveal it2.PeekSpec(), it2.BeforeSpec(), it2.Before'Spec(), it2.PeekModel(), it2.NextModel(), it2.HasPeekModel();
      }
    } else {
      it2.Next();
      newB := b;
      newIt1HasPeek := it1.HasPeek();
      newIt2HasPeek := it2.HasPeek();
      assert (newB ==> it1.Before'() <= it2.Before'()) by {
        reveal DFInv(), LoopSFInv(), LoopTermination();
        reveal it1.PeekSpec(), it1.BeforeSpec(), it1.Before'Spec(), it1.PeekModel(), it1.NextModel(), it1.HasPeekModel();
        reveal it2.PeekSpec(), it2.BeforeSpec(), it2.Before'Spec(), it2.PeekModel(), it2.NextModel(), it2.HasPeekModel();
      }
    }
    assert DFInv(s1, s2)
    by {
      assume false;
      reveal DFInv();
      reveal it1.PeekModel(), it1.NextModel(), it1.HasPeekModel();
      reveal it2.PeekModel(), it2.NextModel(), it2.HasPeekModel();
    }
    assert
      && LoopSFInv(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      && 0 <= LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
        < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))
    by {
      //assume false;
      reveal DFInv(), LoopSFInv(), LoopTermination();
      reveal it1.PeekSpec(), it1.BeforeSpec(), it1.Before'Spec(), it1.PeekModel(), it1.NextModel(), it1.HasPeekModel();
      reveal it2.PeekSpec(), it2.BeforeSpec(), it2.Before'Spec(), it2.PeekModel(), it2.NextModel(), it2.HasPeekModel();
      assert (newB ==> it1.Before'() <= it2.Before'());
      assert (!newB ==> !(it1.Before'() <= s2.Model()));
      if it1.HasPeek?() {
        assert it1.Peek?() !in it2.Before'();
        assert (forall u <- it2.Before'() :: u < it1.Peek?());
      }
    }
  }
}
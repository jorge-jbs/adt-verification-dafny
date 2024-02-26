include "../../src/ADT.dfy"
include "../../src/Collections/KeyValue.dfy"
include "../../src/Collections/SetInt.dfy"

module OrdSetContainedOpaquePrime {
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

    ghost function Before(): set<K>
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()

      ensures Before() < Parent().Model()
      //ensures Traversed() <= Parent().Model()
      //ensures 0 <= |Traversed()| <= |Parent().Model()|

    ghost function Before'(): set<K>
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures Before'() <= Parent().Model()
    {
      if HasPeek?() then
        Before()
      else if PastTheEnd?() then
        Parent().Model()
      else
        {}
    }

    lemma Before'InModel()
      requires Valid()
      requires Parent().Valid()
      ensures Before'() <= Parent().Model()
      ensures 0 <= |Before'()| <= |Parent().Model()|

    ghost function After(): set<K>
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
    {
      Before() - {Peek?()}
    }

    ghost function After'(): set<K>
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
    {
      if HasPeek?() then
        After()
      else if PastTheBeginning?() then
        Parent().Model()
      else
        {}
    }

    opaque ghost predicate PeekSpec(p: K)
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
    {
      && p in Parent().Model()
      && p !in Before()
      && (forall x <- Before() :: x < p)
      && assert p in Parent().Model() - Before();
      && assert Parent().Model() - Before() != {};
      && p == Min(Parent().Model()-Before())
    }

    ghost function Peek?(): K
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures PeekSpec(Peek?())

    lemma PeekInModel()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Peek?() in Parent().Model()

    lemma PeekNotInBefore()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Peek?() !in Before()

    opaque twostate predicate HasPeekBefore()
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
      ensures b == HasPeek?()
      ensures Parent().Iterators() >= old(Parent().Iterators())

      ensures HasPeekBefore()
      /*
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))
      */

    opaque twostate predicate NextBefore()
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
      ensures NextBefore()
      /*
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && (it != this ==> it.Traversed() == old(it.Traversed())
                                   && |it.Traversed()| == old(|it.Traversed()|)
                                   && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?())))
      */

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
      //ensures Parent().Model() == old(Parent().Model())
      //ensures |Parent().Model()| == old(|Parent().Model()|)
      //ensures Traversed() == old(Traversed())
      //ensures |Traversed()| == old(|Traversed()|)

      ensures HasPeek?() // && Peek?()==old(Peek?()) // no debería ser necesario pero lo es
      ensures p == Peek?()

      ensures Parent().Iterators() >= old(Parent().Iterators())
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

  // 2.16M RU (2.6s) - correctness verification
  // 7.65M RU (5.6s) - correctness and functional verification
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
    it1.Before'InModel();
    it2.Before'InModel();
    it1.PeekInModel();
    it1.PeekNotInBefore();
    it1.Next();
    //it1.Before'InModel();
    //it2.Before'InModel();
    newIt1HasPeek := it1.HasPeek();
    //it1.Before'InModel();
    //it2.Before'InModel();
    it2.PeekInModel();
    it2.PeekNotInBefore();
    it2.Next();
    //it1.Before'InModel();
    //it2.Before'InModel();
    newIt2HasPeek := it2.HasPeek();
    it1.Before'InModel();
    it2.Before'InModel();
    newB := b;
    assert
      && DFInv(s1, s2)
    by {
      reveal DFInv();
      reveal it1.NextBefore(), it1.HasPeekBefore();
      reveal it2.NextBefore(), it2.HasPeekBefore();
    }
    assert
      && LoopSFInv(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
      && 0 <= LoopTermination(s1, it1, newIt1HasPeek, s2, it2, newIt2HasPeek, newB)
        < old(LoopTermination(s1, it1, it1HasPeek, s2, it2, it2HasPeek, b))
    by {
      reveal DFInv(), LoopSFInv(), LoopTermination();
      reveal it1.PeekSpec(), it1.NextBefore(), it1.HasPeekBefore();
      reveal it2.PeekSpec(), it2.NextBefore(), it2.HasPeekBefore();
      //assume false;
      assert it1.Before'() <= it2.Before'();
      if it1.HasPeek?() {
        assert it1.Peek?() !in it2.Before'() by {
          assert old(it1.Peek?()) !in old(it2.Before'());
          assert old(it1.Peek?()) !in old(it1.Before'());
          //assert IsMin(s1.Model() - it1.Before(), it1.Peek?());
          assert it1.Peek?() !in it1.Before'();
          assert it2.Before'() == {old(it1.Peek?())} + old(it2.Before'());
          assert it1.Before'() == {old(it1.Peek?())} + old(it1.Before'());
        }
        assert (forall u <- it2.Before'() :: u < it1.Peek?());
      }
    }
  }
}
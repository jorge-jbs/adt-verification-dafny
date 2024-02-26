include "../../src/ADT.dfy"
include "../../src/Collections/KeyValue.dfy"
include "../../src/Collections/SetObject.dfy"

module OrderedSetSpec2 {
  import opened ADT
  import opened KeyValue
  import opened SetObject

  trait OrderedSetIterator {
    ghost function Parent(): OrderedSet

    ghost predicate Valid()
      reads this, Parent(), Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()

    ghost predicate HasPeek?()
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()

    ghost predicate PastTheEnd?()
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures PastTheEnd?() ==> !HasPeek?()

    ghost predicate PastTheBeginning?()
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires !HasPeek?()
    {
      !HasPeek?() && !PastTheEnd?()
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

    opaque ghost function After(): set<K>
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

    opaque ghost predicate PeekSpec(p: K)
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
    {
      && p in Parent().Model()
      && p !in Before()
      && (forall x <- Before() :: x < p)
      && (forall x <- Parent().Model() | x !in Before() :: p <= x)
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
      //ensures Parent() == old(Parent())
      ensures b == HasPeek?() == old(HasPeek?())
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

    opaque twostate predicate PeekModel(p: K)
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
      && p == Peek?() == old(Peek?())
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
      //ensures Parent() == old(Parent())
      ensures HasPeek?()
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures PeekModel(p)
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
      //ensures Parent() == old(Parent())
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

    opaque twostate predicate PrevModel()
      reads this, Parent(), Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
      requires old(HasPeek?())
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && After'() == {old(Peek?())} + old(After())
      && |After'()| == 1 + old(|After()|)
    }

    method Prev()
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
      //ensures Parent() == old(Parent())
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures PrevModel()

    opaque twostate predicate CopyModel()
      reads this, Parent(), Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && Before'() == old(Before'())
      && |Before'()| == old(|Before'()|)
    }

    method Copy()
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      ensures Valid()
      ensures Parent().Valid()
      //ensures Parent() == old(Parent())
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures CopyModel()
  }

  trait OrderedSet extends ADT<set<K>> {
    ghost function Iterators(): set<OrderedSetIterator>
      reads this, Repr()
      requires Valid()
      ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this

    opaque twostate predicate EmptyModel(b: bool)
      reads this, Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && b == (Model() == {})
    }

    opaque twostate predicate SameIteratorModel(it: OrderedSetIterator)
      reads this, Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires it.Valid()
      requires it.HasPeek?() == old(it.HasPeek?())
    {
      && it.Before'() == old(it.Before'())
      && |it.Before'()| == old(|it.Before'()|)
      && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
    }

    opaque twostate predicate SameIterators()
      reads this, Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
    {
      assert old(Allocated(Repr()); true);  // am I breaking something?
      forall it <- old(Iterators()) | old(it.Valid()) ::
        && it.Valid()
        && it.HasPeek?() == old(it.HasPeek?())
        && SameIteratorModel(it)
        //&& it.Parent() == old(it.Parent())
    }

    twostate lemma SameIterator(it: OrderedSetIterator)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires SameIterators()
      ensures it.Valid()
      ensures it.HasPeek?() == old(it.HasPeek?())
      ensures SameIteratorModel(it)
    {
      reveal SameIterators();
    }

    method Empty() returns (b: bool)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures EmptyModel(b)
      ensures SameIterators()

    opaque twostate predicate SizeModel(s: nat)
      reads this, Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && s == |Model()|
    }

    method Size() returns (s: nat)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures SizeModel(s)
      ensures SameIterators()

    opaque twostate predicate FirstModel(new it: OrderedSetIterator)
      reads this, Repr()
      requires old(Valid())
      requires Valid()
      requires it.Valid()
      requires it.Parent() == this
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && it.Before'() == {}
    }

    method First() returns (it: OrderedSetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()

      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures Iterators() >= {it} + old(Iterators())

      ensures FirstModel(it)
      ensures SameIterators()

    opaque twostate predicate LastModel(new it: OrderedSetIterator)
      reads this, Repr()
      requires old(Valid())
      requires Valid()
      requires it.Valid()
      requires it.Parent() == this
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && it.After'() == {}
    }

    method Last() returns (it: OrderedSetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()

      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures Iterators() >= {it} + old(Iterators())

      ensures LastModel(it)

    opaque twostate predicate ContainsModel(k: K, b: bool)
      reads this, Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && b == (k in Model())
    }

    method Contains(k: K) returns (b: bool)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures ContainsModel(k, b)

    opaque twostate predicate AddModel(k: K)
      reads this, Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model()) + {k}
      && if k in old(Model()) then
        |Model()| == old(|Model()|)
      else
        |Model()| == old(|Model()|) + 1
    }

    method Add(k: K)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures AddModel(k)

    opaque twostate predicate RemoveModel(k: K)
      reads this, Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model()) - {k}
      && if k in old(Model()) then
        |Model()| == old(|Model()|) - 1
      else
        |Model()| == old(|Model()|)
    }

    method Remove(k: K)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures RemoveModel(k)

    opaque twostate predicate FindModel(k: K, new it: OrderedSetIterator)
      reads this, Repr()
      requires old(Valid())
      requires Valid()
      requires it.Valid()
      requires it.Parent() == this
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && it.HasPeek?() == (k in old(Model()))
      && if k in old(Model()) then
        it.Peek?() == k
      else
        it.PastTheEnd?()
    }

    method Find(k: K) returns (it: OrderedSetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()

      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures Iterators() >= {it}+old(Iterators())

      ensures FindModel(k, it)

    opaque twostate predicate InsertModel(k: K, new it: OrderedSetIterator)
      reads this, Repr()
      requires old(Valid())
      requires Valid()
      requires it.Valid()
      requires it.Parent() == this
      requires it.HasPeek?()
    {
      && Model() == old(Model()) + {k}
      && (
        if k in old(Model()) then
          |Model()| == old(|Model()|)
        else
          |Model()| == old(|Model()|) + 1
      )
      && it.Peek?() == k
    }

    method Insert(hint: OrderedSetIterator, k: K) returns (it: OrderedSetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires hint.Valid()
      requires hint.Parent() == this
      requires hint in Iterators()

      ensures Valid()
      ensures fresh(it)
      ensures it.Valid() && it.Parent() == this
      ensures it.HasPeek?()
      ensures Iterators() >= {it} + old(Iterators())
      ensures InsertModel(k, it)

    opaque twostate predicate EraseModel(pos: OrderedSetIterator, new it: OrderedSetIterator)
      reads this, Repr()
      requires old(Valid())
      requires Valid()
      requires old(pos.Valid())
      requires pos.Parent() == this
      requires old(pos.HasPeek?())
      requires it.Valid()
      requires it.Parent() == this
    {
      && Model() == old(Model()) - {old(pos.Peek?())}
      && |Model()| == old(|Model()|) - 1
      //&& old(pos.Peek?()) in old(Model())
      && it.Before'() == old(pos.Before())
      && |it.Before'()| == old(|pos.Before()|)
    }

    opaque twostate predicate EraseIteratorModel(it: OrderedSetIterator)
      reads this, Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires it.Valid()
      requires it.HasPeek?() == old(it.HasPeek?())
    {
      true
      /*
      && it.Before'() == old(it.Before'())
      && |it.Before'()| == old(|it.Before'()|)
      && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
      */
    }

    opaque twostate predicate EraseIterators(pos: OrderedSetIterator)
      reads this, Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires old(pos.Valid())
      requires old(pos.HasPeek?())
    {
      var x := old(pos.Peek?());
      assert old(Allocated(Repr()); true);  // am I breaking something?
      forall it <- old(Iterators()) |
          && old(it.Valid())
          && (old(it.HasPeek?()) ==> old(it.Peek?()) != x) ::
        && it.Valid()
        && it.HasPeek?() == old(it.HasPeek?())
        && EraseIteratorModel(it)
        //&& it.Parent() == old(it.Parent())
    }

    twostate lemma EraseIteratorNHP(pos: OrderedSetIterator, it: OrderedSetIterator)
      requires old(Valid())
      requires Valid()
      requires old(pos.Valid())
      requires old(pos.HasPeek?())
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(!it.HasPeek?())
      requires EraseIterators(pos)
      ensures it.Valid()
      ensures !it.HasPeek?()
      ensures EraseIteratorModel(it)
    {
      reveal EraseIterators();
    }

    twostate lemma EraseIteratorHP(pos: OrderedSetIterator, it: OrderedSetIterator)
      requires old(Valid())
      requires Valid()
      requires old(pos.Valid())
      requires old(pos.HasPeek?())
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires old(it.Peek?() != pos.Peek?())
      requires EraseIterators(pos)
      ensures it.Valid()
      ensures it.HasPeek?()
      ensures EraseIteratorModel(it)
    {
      reveal EraseIterators();
    }

    method Erase(pos: OrderedSetIterator) returns (it: OrderedSetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires pos.Valid()
      requires pos.Parent() == this
      requires pos.HasPeek?()
      requires pos in Iterators()

      ensures Valid()
      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures Iterators() >= {it} + old(Iterators())
      ensures EraseModel(pos, it)
      ensures EraseIterators(pos)
  }

  ghost predicate ValidIt(s: OrderedSet, it: OrderedSetIterator)
    reads s, s.Repr()
    requires s.Valid()
  {
    && it.Parent() == s
    && it in s.Iterators()
    && it.Valid()
  }

  ghost predicate Valid2It11(
      a: OrderedSet,
      itA: OrderedSetIterator,
      b: OrderedSet,
      itB: OrderedSetIterator
    )
    reads a, a.Repr(), b, b.Repr()
  {
    && Valid2(a, b)
    && ValidIt(a, itA)
    && ValidIt(b, itB)
  }

  twostate predicate MaintainsValid2It11(
      a: OrderedSet,
      itA: OrderedSetIterator,
      b: OrderedSet,
      itB: OrderedSetIterator
    )
    reads a, a.Repr(), b, b.Repr()
    requires old(Valid2It11(a, itA, b, itB))
  {
    && Valid2It11(a, itA, b, itB)
    && MaintainsValid2(a, b)
    && a.Iterators() >= old(a.Iterators())
    && b.Iterators() >= old(b.Iterators())
  }

  twostate lemma MaintainsValid2It11Helper(
      a: OrderedSet,
      itA: OrderedSetIterator,
      b: OrderedSet,
      itB: OrderedSetIterator
    )
    requires old(Valid2It11(a, itA, b, itB))

    requires a.Valid()
    requires ValidIt(a, itA)
    requires fresh(a.Repr() - old(a.Repr()))
    requires a.Iterators() >= old(a.Iterators())

    requires old(allocated(a.Repr()))
    requires old(allocated(b.Repr()))
    requires allocated(b.Repr())
    requires b.Repr() == old(b.Repr())
    requires unchanged({b} + b.Repr())

    ensures MaintainsValid2It11(a, itA, b, itB)
    ensures allocated(a.Repr())
    ensures allocated(b.Repr())
  {}

  ghost predicate ValidIt2(
      a: OrderedSet,
      itA: OrderedSetIterator,
      itB: OrderedSetIterator
    )
    reads a, a.Repr()
  {
    && a.Valid()
    && ValidIt(a, itA)
    && ValidIt(a, itB)
  }
}
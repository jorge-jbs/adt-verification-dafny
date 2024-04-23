include "../../src/AdtWithoutThis.dfy"
include "../../src/Collections/KeyValue.dfy"
include "../../src/Collections/SetObject.dfy"

module UnorderedMapSpec {
  import opened ADT
  import opened KeyValue
  import opened SetObject

  trait {:termination false} UnorderedMapIterator {
    ghost function Parent(): UnorderedMap

    ghost predicate Valid()
      reads Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()

    ghost predicate HasPeek?()
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()

    opaque ghost predicate BeforeSpec(before: set<K>)
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
    {
      && before < Parent().Model().Keys
      && |before| < |Parent().Model()|
    }

    ghost function Before(): set<K>
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures BeforeSpec(Before())

    opaque ghost predicate TraversedSpec(traversed: set<K>)
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
    {
      && traversed <= Parent().Model().Keys
      && |traversed| <= |Parent().Model()|
    }

    /*
    Helper function that specifies what elements have been traversed while
    iterating the map from back to front, by repeatedly calling `Next`.

    It is, essentially, a total version of `Before`.
    */
    ghost function Traversed(): set<K>
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures TraversedSpec(Traversed())
    {
      if HasPeek?() then
        assert TraversedSpec(Before()) by { reveal BeforeSpec(), TraversedSpec(); }
        Before()
      else
        assert TraversedSpec(Parent().Model().Keys) by { reveal BeforeSpec(), TraversedSpec(); }
        Parent().Model().Keys
    }

    opaque ghost predicate PeekSpec(p: (K, V))
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
    {
      && p in Parent().Model().Items
      && p.0 !in Before()
    }

    ghost function Peek?(): (K, V)
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures PeekSpec(Peek?())

    opaque twostate predicate HasPeekModel()
      reads Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && HasPeek?() == old(HasPeek?())
      && (old(HasPeek?()) ==>
        && Peek?() == old(Peek?())
        && Before() == old(Before())
        && |Before()| == old(|Before()|)
      )
    }

    method HasPeek() returns (b: bool)
      modifies Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      ensures Valid()
      ensures Parent().Valid()
      ensures b == HasPeek?()
      ensures Parent().Iterators() >= old(Parent().Iterators())

      ensures HasPeekModel()
      ensures Parent().SameIterators()

    opaque twostate predicate PeekModel(new p: (K, V))
      reads Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
      requires old(HasPeek?())
      requires HasPeek?()
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && Before() == old(Before())
      && |Before()| == old(|Before()|)
      && p == Peek?() == old(Peek?())
    }

    method Peek() returns (p: (K, V))
      modifies Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      ensures HasPeek?()
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures PeekModel(p)
      ensures Parent().SameIterators()

    opaque twostate predicate NextModel()
      reads Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
      requires old(HasPeek?())
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && Traversed() == {old(Peek?().0)} + old(Before())
      && |Traversed()| == 1 + old(|Before()|)
    }

    opaque twostate predicate NextIterators()
      reads Parent().Repr()
      requires old(Parent().Valid())
      requires Parent().Valid()
      requires fresh(Parent().Repr() - old(Parent().Repr()))
      requires Parent().Iterators() >= old(Parent().Iterators())
    {
      assert old(allocated(Parent().Repr()));
      forall it <- old(Parent().Iterators()) | old(it.Valid()) ::
        && it.Valid()
        && (it != this ==> Parent().SameIteratorModel(it))
    }

    twostate lemma NextIterator(it: UnorderedMapIterator)
      requires old(Parent().Valid())
      requires Parent().Valid()
      requires fresh(Parent().Repr() - old(Parent().Repr()))
      requires Parent().Iterators() >= old(Parent().Iterators())
      requires it in old(Parent().Iterators())
      requires old(it.Valid())
      requires NextIterators()
      requires it != this
      ensures it.Valid()
      ensures Parent().SameIteratorModel(it)
    {
      reveal NextIterators();
    }

    method Next()
      modifies Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures NextModel()
      ensures NextIterators()

    opaque twostate predicate CopyModel(new it: UnorderedMapIterator)
      reads Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Parent().Valid()
      requires Valid()
      requires it.Parent() == Parent()
      requires it.Valid()
      requires it.HasPeek?() == HasPeek?()
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && HasPeek?() == old(HasPeek?())
      && (HasPeek?() ==>
        && Peek?() == old(Peek?())
        && Before() == old(Before())
        && |Before()| == old(|Before()|)
        && it.Before() == Before()
      )
    }

    method Copy() returns (it: UnorderedMapIterator)
      modifies Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures fresh(it)
      ensures it != this
      ensures it.Valid()
      ensures it.Parent() == Parent()
      ensures it.HasPeek?() == HasPeek?()
      ensures CopyModel(it)
      ensures Parent().SameIterators()
  }

  trait {:termination false} UnorderedMap extends ADT<map<K, V>> {
    ghost function Iterators(): set<UnorderedMapIterator>
      reads Repr()
      requires Valid()
      ensures forall it <- Iterators() :: it in Repr() && it.Parent() == this

    opaque twostate predicate SameIteratorModel(it: UnorderedMapIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires it.Valid()
    {
      && it.HasPeek?() == old(it.HasPeek?())
      && (it.HasPeek?() ==>
        && it.Peek?() == old(it.Peek?())
        && it.Before() == old(it.Before())
        && |it.Before()| == old(|it.Before()|)
      )
    }

    opaque twostate predicate SameIterators()
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
    {
      assert old(allocated(Repr()));
      forall it <- old(Iterators()) | old(it.Valid()) ::
        && it.Valid()
        && SameIteratorModel(it)
    }

    twostate lemma SameIterator(it: UnorderedMapIterator)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires SameIterators()
      ensures it.Valid()
      ensures SameIteratorModel(it)
    {
      reveal SameIterators();
    }

    opaque twostate predicate EmptyModel(b: bool)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && b == (Model() == map[])
    }

    method Empty() returns (b: bool)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures EmptyModel(b)
      ensures SameIterators()

    opaque twostate predicate SizeModel(s: nat)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && s == |Model()|
    }

    method Size() returns (s: nat)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures SizeModel(s)
      ensures SameIterators()

    opaque twostate predicate FirstModel(new it: UnorderedMapIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires it.Valid()
      requires it.Parent() == this
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && it.Traversed() == {}
    }

    method First() returns (it: UnorderedMapIterator)
      modifies Repr()
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

    opaque twostate predicate ContainsModel(k: K, b: bool)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && b == (k in Model())
    }

    method Contains(k: K) returns (b: bool)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures ContainsModel(k, b)
      ensures SameIterators()

    opaque ghost predicate AtModelPre(k: K)
      reads Repr()
      requires Valid()
    {
      k in Model()
    }

    opaque twostate predicate AtModel(k: K, v: V)
      reads Repr()
      requires old(Valid())
      requires old(AtModelPre(k))
      requires Valid()
    {
      reveal AtModelPre();
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && v == Model()[k]
    }

    method At(k: K) returns (v: V)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires AtModelPre(k)
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures AtModel(k, v)
      ensures SameIterators()

    opaque twostate predicate FindModel(k: K, new it: UnorderedMapIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires it.Valid()
      requires it.Parent() == this
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && it.HasPeek?() == (k in old(Model()))
      && (it.HasPeek?() ==> it.Peek?().0 == k)
    }

    method Find(k: K) returns (it: UnorderedMapIterator)
      modifies Repr()
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
      ensures SameIterators()

    opaque twostate predicate AddModel(k: K, v: V)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model()) + map[k := v]
      && if k in old(Model()) then
        |Model()| == old(|Model()|)
      else
        |Model()| == old(|Model()|) + 1
    }

    method Add(k: K, v: V)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures AddModel(k, v)

    opaque twostate predicate RemoveModel(k: K)
      reads Repr()
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
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures RemoveModel(k)

    opaque twostate predicate InsertModel(k: K, v: V, new it: UnorderedMapIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires it.Valid()
      requires it.Parent() == this
      requires it.HasPeek?()
    {
      && Model() == old(Model()) + map[k := v]
      && it.Peek?().0 == k
      && if k in old(Model()) then
        |Model()| == old(|Model()|)
      else
        |Model()| == old(|Model()|) + 1
    }

    method Insert(hint: UnorderedMapIterator, k: K, v: V) returns (it: UnorderedMapIterator)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires hint.Valid()
      requires hint.Parent() == this
      requires hint in Iterators()

      ensures Valid()
      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures it.HasPeek?()
      ensures Iterators() >= {it} + old(Iterators())
      ensures InsertModel(k, v, it)

    opaque twostate predicate EraseModel(pos: UnorderedMapIterator, new it: UnorderedMapIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires old(pos.Valid())
      requires pos.Parent() == this
      requires old(pos.HasPeek?())
      requires it.Valid()
      requires it.Parent() == this
    {
      && Model() == old(Model()) - {old(pos.Peek?().0)}
      && |Model()| == old(|Model()|) - 1
      && it.Traversed() == old(pos.Before())
      && |it.Traversed()| == old(|pos.Before()|)
    }

    method Erase(pos: UnorderedMapIterator) returns (it: UnorderedMapIterator)
      modifies Repr()
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
  }

  ghost predicate ValidIt(s: UnorderedMap, it: UnorderedMapIterator)
    reads s.Repr()
    requires s.Valid()
  {
    && it.Parent() == s
    && it in s.Iterators()
    && it.Valid()
  }

  ghost predicate Valid1It1(s: UnorderedMap, it: UnorderedMapIterator)
    reads s.Repr()
  {
    s.Valid() && ValidIt(s, it)
  }
}
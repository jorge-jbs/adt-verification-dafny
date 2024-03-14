include "../Collections/Seq.dfy"
include "../Collections/KeyValue.dfy"
include "../UnorderedMap/UnorderedMapSpec.dfy"
include "../OrderedMap/OrderedMapSpec.dfy"

module TreeMapSpec {
  import opened Seq
  import opened SetObject
  import opened KeyValue
  import opened UnorderedMapSpec
  import opened OrderedMapSpec

  trait {:termination false} TreeMap extends OrderedMap {
    opaque twostate predicate AddIteratorModel(it: UnorderedMapIterator, k: K, v: V)
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
        && it.Peek?().0 == old(it.Peek?().0)
        && if k in old(Model()) && k == it.Peek?().0 then
          it.Peek?().1 == v
        else
          it.Peek?().1 == old(it.Peek?().1)
      )
      && if k in old(Model()) || (it.HasPeek?() && it.Peek?().0 < k) then
        && it.Traversed() == old(it.Traversed())
        && |it.Traversed()| == old(|it.Traversed()|)
      else
        && it.Traversed() == old(it.Traversed()) + {k}
        && |it.Traversed()| == old(|it.Traversed()|) + 1
    }

    opaque twostate predicate AddIterators(k: K, v: V)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
    {
      assert old(allocated(Repr()));
      forall it <- old(Iterators()) | old(it.Valid()) ::
        && it.Valid()
        && AddIteratorModel(it, k, v)
    }

    twostate lemma AddIterator(it: UnorderedMapIterator, k: K, v: V)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires AddIterators(k, v)
      ensures it.Valid()
      ensures AddIteratorModel(it, k, v)
    {
      reveal AddIterators();
    }

    twostate lemma AddIteratorHasPeek(it: UnorderedMapIterator, k: K, v: V)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires AddIterators(k, v)
      ensures it.Valid()
      ensures it.HasPeek?()
      ensures AddIteratorModel(it, k, v)
    {
      reveal AddIterators();
      reveal AddIteratorModel();
    }

    twostate lemma AddIteratorNotHasPeek(it: UnorderedMapIterator, k: K, v: V)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(!it.HasPeek?())
      requires AddIterators(k, v)
      ensures it.Valid()
      ensures !it.HasPeek?()
      ensures AddIteratorModel(it, k, v)
    {
      reveal AddIterators();
      reveal AddIteratorModel();
    }

    opaque twostate predicate AddIteratorLtModelPre(it: UnorderedMapIterator, k: K, v: V)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires it.Valid()
      requires AddIterators(k, v)
    {
      assert it.HasPeek?() by { reveal AddIterators(), AddIteratorModel(); }
      it.Peek?().0 < k
    }

    opaque twostate predicate AddIteratorLtModel(it: UnorderedMapIterator, k: K, v: V)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires it.Valid()
      requires it.HasPeek?()
      requires AddIterators(k, v)
    {
      && it.Before() == old(it.Before())
      && |it.Before()| == old(|it.Before()|)
    }

    twostate lemma AddIteratorLt(it: UnorderedMapIterator, k: K, v: V)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires AddIterators(k, v)
      requires it.Valid()
      requires AddIteratorLtModelPre(it, k, v)
      ensures it.Valid()
      ensures it.HasPeek?()
      ensures AddIteratorLtModel(it, k, v)
    {
      reveal AddIterators();
      reveal AddIteratorModel();
      reveal AddIteratorLtModelPre();
      reveal AddIteratorLtModel();
    }

    opaque twostate predicate AddIteratorGtModelPre(it: UnorderedMapIterator, k: K, v: V)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires it.Valid()
      requires AddIterators(k, v)
    {
      assert it.HasPeek?() by { reveal AddIterators(), AddIteratorModel(); }
      && k !in old(Model())
      && k < it.Peek?().0
    }

    opaque twostate predicate AddIteratorGtModel(it: UnorderedMapIterator, k: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires it.Valid()
      requires it.HasPeek?()
    {
      && it.Before() == old(it.Before()) + {k}
      && |it.Before()| == old(|it.Before()|) + 1
    }

    twostate lemma AddIteratorGt(it: UnorderedMapIterator, k: K, v: V)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires AddIterators(k, v)
      requires it.Valid()
      requires AddIteratorGtModelPre(it, k, v)
      ensures it.Valid()
      ensures it.HasPeek?()
      ensures AddIteratorGtModel(it, k)
    {
      reveal AddIterators();
      reveal AddIteratorModel();
      reveal AddIteratorGtModelPre();
      reveal AddIteratorGtModel();
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
      ensures AddIterators(k, v)

    opaque ghost predicate RemoveIteratorModelPre(it: UnorderedMapIterator, k: K)
      reads Repr()
      requires Valid()
      requires it in Iterators()
      requires it.Valid()
    {
      it.HasPeek?() ==> it.Peek?().0 != k
    }

    opaque twostate predicate RemoveIteratorModel(it: UnorderedMapIterator, k: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires it.Valid()
    {
      && it.HasPeek?() == old(it.HasPeek?())
      && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
      && (
        if k in old(Model()) && (it.HasPeek?() ==> k < it.Peek?().0) then
          && it.Traversed() == old(it.Traversed()) - {k}
          && |it.Traversed()| == old(|it.Traversed()|) - 1
        else
          && it.Traversed() == old(it.Traversed())
          && |it.Traversed()| == old(|it.Traversed()|)
      )
    }

    opaque twostate predicate RemoveIterators(k: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
    {
      assert old(allocated(Repr()));
      forall it <- old(Iterators()) | old(it.Valid()) && (old(it.HasPeek?()) ==> old(it.Peek?().0) != k) ::
        && it.Valid()
        && RemoveIteratorModel(it, k)
    }

    twostate lemma RemoveIterator(it: UnorderedMapIterator, k: K)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires RemoveIterators(k)
      requires old(RemoveIteratorModelPre(it, k))
      ensures it.Valid()
      ensures RemoveIteratorModel(it, k)
    {
      reveal RemoveIterators(), RemoveIteratorModelPre(), RemoveIteratorModel();
    }

    twostate lemma RemoveIteratorHasPeek(it: UnorderedMapIterator, k: K)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires RemoveIterators(k)
      requires old(RemoveIteratorModelPre(it, k))
      ensures it.Valid()
      ensures it.HasPeek?()
      ensures RemoveIteratorModel(it, k)
    {
      reveal RemoveIterators();
      reveal RemoveIteratorModelPre();
      reveal RemoveIteratorModel();
    }

    twostate lemma RemoveIteratorNotHasPeek(it: UnorderedMapIterator, x: K)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(!it.HasPeek?())
      requires RemoveIterators(x)
      ensures it.Valid()
      ensures !it.HasPeek?()
      ensures RemoveIteratorModel(it, x)
    {
      reveal RemoveIterators();
      reveal RemoveIteratorModel();
    }

    opaque twostate predicate RemoveIteratorLtModelPre(it: UnorderedMapIterator, k: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires it.Valid()
      requires RemoveIterators(k)
    {
      k !in old(Model()) || old(it.Peek?().0 < k)
    }

    opaque twostate predicate RemoveIteratorLtModel(it: UnorderedMapIterator, x: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires it.Valid()
      requires it.HasPeek?()
      requires RemoveIterators(x)
    {
      && it.Before() == old(it.Before())
      && |it.Before()| == old(|it.Before()|)
    }

    twostate lemma RemoveIteratorLt(it: UnorderedMapIterator, k: K)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires RemoveIterators(k)
      requires it.Valid()
      requires RemoveIteratorLtModelPre(it, k)
      ensures it.Valid()
      ensures it.HasPeek?()
      ensures RemoveIteratorLtModel(it, k)
    {
      reveal RemoveIterators();
      reveal RemoveIteratorModel();
      reveal RemoveIteratorLtModelPre();
      reveal RemoveIteratorLtModel();
      reveal it.PeekSpec();
    }

    opaque twostate predicate RemoveIteratorGtModelPre(it: UnorderedMapIterator, k: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires it.Valid()
      requires RemoveIterators(k)
    {
      && k in old(Model())
      && k < old(it.Peek?().0)
    }

    opaque twostate predicate RemoveIteratorGtModel(it: UnorderedMapIterator, k: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires it.Valid()
      requires it.HasPeek?()
      requires RemoveIterators(k)
    {
      && it.Before() == old(it.Before()) - {k}
      && |it.Before()| == old(|it.Before()|) - 1
    }

    twostate lemma RemoveIteratorGt(it: UnorderedMapIterator, k: K)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires RemoveIterators(k)
      requires it.Valid()
      requires RemoveIteratorGtModelPre(it, k)
      ensures it.Valid()
      ensures it.HasPeek?()
      ensures RemoveIteratorGtModel(it, k)
    {
      reveal RemoveIterators();
      reveal RemoveIteratorModel();
      reveal RemoveIteratorGtModelPre();
      reveal RemoveIteratorGtModel();
    }

    opaque ghost predicate RemoveIteratorTraversedShrinksModelPre(it: UnorderedMapIterator, k: K)
      reads Repr()
      requires Valid()
      requires it in Iterators()
      requires it.Valid()
      requires it.Valid()
    {
      && k in Model()
      && (it.HasPeek?() ==> k < it.Peek?().0)
    }

    opaque twostate predicate RemoveIteratorTraversedShrinksModel(it: UnorderedMapIterator, k: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires it.Valid()
    {
      && it.Traversed() == old(it.Traversed()) - {k}
      && |it.Traversed()| == old(|it.Traversed()|) - 1
    }

    twostate lemma RemoveIteratorTraversedShrinks(it: UnorderedMapIterator, k: K)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires RemoveIterators(k)
      requires old(RemoveIteratorTraversedShrinksModelPre(it, k))
      ensures it.Valid()
      ensures RemoveIteratorTraversedShrinksModel(it, k)
    {
      reveal RemoveIterators();
      reveal RemoveIteratorModel();
      reveal RemoveIteratorTraversedShrinksModelPre();
      reveal RemoveIteratorTraversedShrinksModel();
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
      ensures RemoveIterators(k)

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
      ensures AddIterators(k, v)

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
      ensures RemoveIterators(old(pos.Peek?().0))
  }
}
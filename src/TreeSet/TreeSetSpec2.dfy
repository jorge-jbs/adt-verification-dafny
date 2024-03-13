include "../Collections/Seq.dfy"
include "../Collections/KeyValue.dfy"
include "../UnorderedSet/UnorderedSetSpec2.dfy"
include "../OrderedSet/OrderedSetSpec2.dfy"

module TreeSetSpec {
  import opened Seq
  import opened SetObject
  import opened KeyValue
  import opened UnorderedSetSpec2
  import opened OrderedSetSpec2

  trait {:termination false} TreeSet extends OrderedSet {
    opaque twostate predicate AddIteratorModel(it: UnorderedSetIterator, k: K)
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
      && if k in old(Model()) || (it.HasPeek?() && it.Peek?() < k) then
        && it.Traversed() == old(it.Traversed())
        && |it.Traversed()| == old(|it.Traversed()|)
      else
        && it.Traversed() == old(it.Traversed()) + {k}
        && |it.Traversed()| == old(|it.Traversed()|) + 1
    }

    opaque twostate predicate AddIterators(x: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
    {
      assert old(Allocated(Repr()); true);  // am I breaking something?
      forall it <- old(Iterators()) | old(it.Valid()) ::
        && it.Valid()
        && AddIteratorModel(it, x)
        //&& it.Parent() == old(it.Parent())
    }

    twostate lemma AddIterator(it: UnorderedSetIterator, x: K)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires AddIterators(x)
      ensures it.Valid()
      ensures AddIteratorModel(it, x)
    {
      reveal AddIterators();
    }

    twostate lemma AddIteratorHasPeek(it: UnorderedSetIterator, x: K)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires AddIterators(x)
      ensures it.Valid()
      ensures it.HasPeek?()
      ensures AddIteratorModel(it, x)
    {
      reveal AddIterators();
      reveal AddIteratorModel();
    }

    twostate lemma AddIteratorNotHasPeek(it: UnorderedSetIterator, x: K)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(!it.HasPeek?())
      requires AddIterators(x)
      ensures it.Valid()
      ensures !it.HasPeek?()
      ensures AddIteratorModel(it, x)
    {
      reveal AddIterators();
      reveal AddIteratorModel();
    }

    opaque twostate predicate AddIteratorLtModelPre(it: UnorderedSetIterator, x: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires it.Valid()
      requires AddIterators(x)
    {
      assert it.HasPeek?() by { reveal AddIterators(), AddIteratorModel(); }
      it.Peek?() < x
    }

    opaque twostate predicate AddIteratorLtModel(it: UnorderedSetIterator, x: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires it.Valid()
      requires it.HasPeek?()
      requires AddIterators(x)
    {
      && it.Before() == old(it.Before())
      && |it.Before()| == old(|it.Before()|)
    }

    twostate lemma AddIteratorLt(it: UnorderedSetIterator, x: K)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires AddIterators(x)
      requires it.Valid()
      requires AddIteratorLtModelPre(it, x)
      ensures it.Valid()
      ensures it.HasPeek?()
      ensures AddIteratorLtModel(it, x)
    {
      reveal AddIterators();
      reveal AddIteratorModel();
      reveal AddIteratorLtModelPre();
      reveal AddIteratorLtModel();
    }

    opaque twostate predicate AddIteratorGtModelPre(it: UnorderedSetIterator, x: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires it.Valid()
      requires AddIterators(x)
    {
      assert it.HasPeek?() by { reveal AddIterators(), AddIteratorModel(); }
      && x !in old(Model())
      && x < it.Peek?()
    }

    opaque twostate predicate AddIteratorGtModel(it: UnorderedSetIterator, x: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires it.Valid()
      requires it.HasPeek?()
      requires AddIterators(x)
    {
      && it.Before() == old(it.Before()) + {x}
      && |it.Before()| == old(|it.Before()|) + 1
    }

    twostate lemma AddIteratorGt(it: UnorderedSetIterator, x: K)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires AddIterators(x)
      requires it.Valid()
      requires AddIteratorGtModelPre(it, x)
      ensures it.Valid()
      ensures it.HasPeek?()
      ensures AddIteratorGtModel(it, x)
    {
      reveal AddIterators();
      reveal AddIteratorModel();
      reveal AddIteratorGtModelPre();
      reveal AddIteratorGtModel();
    }

    method Add(k: K)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures AddModel(k)
      ensures AddIterators(k)

    opaque ghost predicate RemoveIteratorModelPre(it: UnorderedSetIterator, k: K)
      reads Repr()
      requires Valid()
      requires it in Iterators()
      requires it.Valid()
      //requires old(it.HasPeek?()) ==> old(it.Peek?().0) != k
    {
      it.HasPeek?() ==> it.Peek?() != k
    }

    opaque twostate predicate RemoveIteratorModel(it: UnorderedSetIterator, k: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires it.Valid()
      //requires old(it.HasPeek?()) ==> old(it.Peek?().0) != k
    {
      && it.HasPeek?() == old(it.HasPeek?())
      && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
      && (
        if k in old(Model()) && (it.HasPeek?() ==> k < it.Peek?()) then
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
      assert old(Allocated(Repr()); true);  // am I breaking something?
      forall it <- old(Iterators()) | old(it.Valid()) && (old(it.HasPeek?()) ==> old(it.Peek?()) != k) ::
        && it.Valid()
        && RemoveIteratorModel(it, k)
        //&& it.Parent() == old(it.Parent())
    }

    twostate lemma RemoveIterator(it: UnorderedSetIterator, k: K)
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

    method Insert(hint: UnorderedSetIterator, k: K) returns (it: UnorderedSetIterator)
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
      ensures it.Valid() && it.Parent() == this
      ensures it.HasPeek?()
      ensures Iterators() >= {it} + old(Iterators())
      ensures InsertModel(k, it)
      ensures AddIterators(k)

    method Erase(pos: UnorderedSetIterator) returns (it: UnorderedSetIterator)
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
      ensures RemoveIterators(old(pos.Peek?()))
  }
}
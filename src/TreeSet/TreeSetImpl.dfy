include "../../src/ADT.dfy"
include "../../src/Collections/KeyValue.dfy"
include "../../src/TreeMap/TreeMapImpl.dfy"
include "../../src/TreeMap/TreeMapSpec.dfy"
include "../../src/UnorderedSet/UnorderedSetSpec.dfy"
include "../../src/UnorderedMap/UnorderedMapSpec.dfy"
include "../../src/OrderedSet/OrderedSetSpec.dfy"
include "../../src/OrderedMap/OrderedMapSpec.dfy"

module TreeSetImpl {
  import opened TreeMapImpl
  import opened TreeMapSpec
  import opened UnorderedSetSpec
  import opened UnorderedMapSpec
  import opened OrderedSetSpec
  import opened OrderedMapSpec
  import opened ADT
  import opened KeyValue

  class TreeSetIteratorImpl extends OrderedSetIterator {
    const iter: TreeMapIteratorImpl
    ghost const parent: TreeSetImpl

    constructor (ghost parent: TreeSetImpl, iter: TreeMapIteratorImpl)
      modifies parent`iterators
      requires allocated(parent.Repr())
      ensures fresh(parent.Repr() - old(parent.Repr()))
      ensures allocated(parent.Repr())

      requires parent.Valid()
      requires iter.Valid()
      requires iter.Parent() == parent.treemap
      requires forall it <- parent.iterators :: it.iter != iter

      ensures parent.Valid()
      ensures parent.Model() == old(parent.Model())
      ensures |parent.Model()| == |old(parent.Model())|

      ensures Valid()
      ensures this.parent == parent
      ensures this.iter == iter

      ensures HasPeek?() == iter.HasPeek?()
      ensures HasPeek?() ==> Peek?() == iter.Peek?().0
      ensures Index() == iter.Index()
      ensures parent.iterators == {this} + old(parent.iterators)
      ensures forall it <- old(parent.Iterators()) | old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (it.HasPeek?() <==> old(it.HasPeek?()))
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))
      ensures forall it <- old(parent.Iterators()) | old(it.Valid()) ::
                (it is OrderedSetIterator &&
                 (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index()))
    {
      this.iter := iter;
      this.parent := parent;
      new;
      parent.iterators := parent.iterators + {this};
    }

    ghost function Parent(): UnorderedSet
      reads this
      ensures Parent() is OrderedSet
    {
      parent
    }

    ghost predicate Valid()
      reads this, Parent(), Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()
    {
      && this in parent.iterators
      && parent.Valid()
      && iter.parent == parent.treemap
      && iter.Valid()
    }

    //Index -1 means past the beginning. Traversed is empty. No Peek
    //Index |Parent().Model()| means past the end- Traversed is Parent().Model(). No Peek
    // 0<=Index <|Parent().Model()| Peek is the Index()-th elem which is also the size of Traversed()
    //i.e. the set of elements smaller than the Peek

    //When HasPeek is true the iterator
    // is uniquely determined either by
    // Index(), Traversed() or Peek?()
    //When HasPeek is not true we need Index

    ghost function Index(): int
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures -1 <= Index() <= |Parent().Model()|
    {
      iter.Index()
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
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)

      ensures Traversed() == old(Traversed())
      ensures |Traversed()| == old(|Traversed()|)
      ensures Index() == old(Index())
      ensures old(HasPeek?()) ==> HasPeek?() && Peek?()==old(Peek?())
      ensures b == HasPeek?()

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it is OrderedSetIterator
                && (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index())

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
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)

      ensures Traversed() == {old(Peek?())} + old(Traversed())
      ensures |Traversed()| == 1 + |old(Traversed())|
      ensures Index() == old(Index()) + 1

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && (it != this ==> it.Traversed() == old(it.Traversed())
                                   && |it.Traversed()| == old(|it.Traversed()|)
                                   && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?())))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) && it != this ::
                && it is OrderedSetIterator
                && (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index())
    {
      assert parent !in iter.parent.Repr();
      iter.Next();
    }

    method Peek() returns (k: K)
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
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)

      ensures Index() == old(Index())

      ensures Traversed() == old(Traversed())
      ensures |Traversed()| == old(|Traversed()|)

      ensures HasPeek?() && Peek?() == old(Peek?())
      ensures k == Peek?()

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it is OrderedSetIterator
                && (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index())
    {
      assert parent !in iter.parent.Repr();
      var p := iter.Peek();
      return p.0;
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
      ensures Parent() == old(Parent())
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)

      ensures Index() == old(Index()) - 1

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && (it != this ==> it.Traversed() == old(it.Traversed())
                                   && |it.Traversed()| == old(|it.Traversed()|)
                                   && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?())))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) && it != this ::
                && it is OrderedSetIterator
                && (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index())
    {
      assert parent !in iter.parent.Repr();
      iter.Prev();
    }

    method Copy() returns (it: UnorderedSetIterator)
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      ensures fresh(it)
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)

      ensures Index() == old(Index())

      ensures Traversed() == old(Traversed())
      ensures |Traversed()| == old(|Traversed()|)

      ensures old(HasPeek?()) ==> HasPeek?() && Peek?()==old(Peek?())

      ensures it.Valid()
      ensures Parent() == it.Parent()
      ensures it is OrderedSetIterator
      ensures  (it as OrderedSetIterator).Index() == Index()
      ensures Traversed() == it.Traversed()
      ensures |Traversed()| == |it.Traversed()|
      ensures HasPeek?() ==> it.HasPeek?() && Peek?()==it.Peek?()

      ensures Parent().Iterators() >= {it} + old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it is OrderedSetIterator
                && (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index())
    {
      assert parent !in iter.parent.Repr();
      var iter: UnorderedMapIterator := iter.Copy();
      it := new TreeSetIteratorImpl(parent, iter);
    }
  }

  class TreeSetImpl extends OrderedSet {
    const treemap: TreeMapImpl
    ghost var iterators: set<TreeSetIteratorImpl>

    ghost function ReprFamily(n: nat): set<object>
      decreases n
      ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
      reads this, if n == 0 then {} else ReprFamily(n-1)
    {
      if n == 0 then
        {treemap} + iterators
      else if n == 1 then
        {treemap} + iterators + (set it <- iterators :: it.iter)
      else
        {treemap} + iterators + (set it <- iterators :: it.iter) + treemap.ReprFamily(n-2)
    }

    ghost predicate Valid()
      reads this, Repr()
    {
      && ReprDepth == treemap.ReprDepth + 2
      && assert ReprFamily(0) <= ReprFamily(ReprDepth); true
      && treemap.Valid()
      && (forall it | it in iterators :: it.parent == this)
      && (forall it | it in iterators :: it.iter in treemap.iterators)
      && (
        forall it1 <- iterators, it2 <- iterators | && it1 != it2 ::
          it1.iter != it2.iter
      )
    }

    ghost function Model(): set<K>
      reads this, Repr()
      requires Valid()
    {
      treemap.Model().Keys
    }

    constructor()
      ensures Valid()
      ensures Model() == {}
      ensures fresh(Repr())
    {
      var treemap := new TreeMapImpl();
      ReprDepth := treemap.ReprDepth + 2;
      this.treemap := treemap;
      this.iterators := {};
      new;
      assert Repr() == {treemap} + iterators + (set it <- iterators :: it.iter) + treemap.Repr();
    }

    method Size() returns (s: nat)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures s == |Model()|

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it is OrderedSetIterator
                && (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index())
    {
      assert this !in treemap.Repr();
      s := treemap.Size();
    }

    ghost function Iterators(): set<UnorderedSetIterator>
      reads this, Repr()
      requires Valid()
      ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
    {
      iterators
    }

    method Empty() returns (b: bool)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures b == Empty?()

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it is OrderedSetIterator
                && (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index())
    {
      assert this !in treemap.Repr();
      b := treemap.Empty();
      assert Valid();
      assert b == (Model() == {}) == Empty?();
    }

    method First() returns (it: UnorderedSetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures it is OrderedSetIterator
      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures it.Traversed() == {}
      ensures (it as OrderedSetIterator).Index() == 0

      ensures Iterators() >= {it} + old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it is OrderedSetIterator
                && (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index())
    {
      assert this !in treemap.Repr();
      var iter: UnorderedMapIterator := treemap.First();
      var iter': OrderedMapIterator := iter as OrderedMapIterator;
      var iter'': TreeMapIteratorImpl := iter' as TreeMapIteratorImpl;
      var it' := new TreeSetIteratorImpl(this, iter'');
      return it' as UnorderedSetIterator;
    }

    method Last() returns (it: OrderedSetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures it is OrderedSetIterator
      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures it.Index() ==  |Model()|-1

      ensures Iterators() >= {it} + old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it is OrderedSetIterator
                && (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index())
    {
      assert this !in treemap.Repr();
      var iter: UnorderedMapIterator := treemap.Last();
      var iter': OrderedMapIterator := iter as OrderedMapIterator;
      var iter'': TreeMapIteratorImpl := iter' as TreeMapIteratorImpl;
      var it' := new TreeSetIteratorImpl(this, iter'');
      return it' as UnorderedSetIterator;
    }

    method Contains(x: K) returns (b: bool)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures b == (x in Model())

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it is OrderedSetIterator
                && (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index())
    {
      assert this !in treemap.Repr();
      b := treemap.Contains(x);
    }

    method Add(x: K)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model()) + {x}
      ensures if (x in old(Model())) then |Model()| == old(|Model()|)
              else |Model()| == 1 + old(|Model()|)

      ensures Iterators() >= old(Iterators())
    {
      assert this !in treemap.Repr();
      treemap.Add(x, 0);
    }

    method Remove(x: K)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model()) - {x}
      ensures if (x in old(Model())) then |Model()| == old(|Model()|) - 1
              else |Model()| == old(|Model()|)

      ensures Iterators() >= old(Iterators())
    {
      assert this !in treemap.Repr();
      treemap.Remove(x);
    }

    method Find(x: K) returns (newt: UnorderedSetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent() == this
      ensures x in old(Model()) ==> newt.HasPeek?() && newt.Peek?() == x
      ensures x !in old(Model()) ==> newt.Traversed() == Model() && |newt.Traversed()| == |Model()|

      ensures Iterators() >= {newt}+old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))
    {
      assert this !in treemap.Repr();
      var iter: UnorderedMapIterator := treemap.Find(x);
      newt := new TreeSetIteratorImpl(this, iter);
    }

    method Insert(mid: UnorderedSetIterator, x: K) returns (newt: UnorderedSetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model()) + {x}
      ensures if (x in old(Model())) then |Model()| == old(|Model()|)
              else |Model()| == 1 + old(|Model()|)

      requires mid.Valid()
      requires mid.Parent() == this
      requires mid in Iterators()

      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent() == this
      ensures newt.HasPeek?() && newt.Peek?() == x

      ensures Iterators() >= {newt}+old(Iterators())
    {
      assert this !in treemap.Repr();
      var iter: UnorderedMapIterator := treemap.Insert((mid as TreeSetIteratorImpl).iter, x, 0);
      newt := new TreeSetIteratorImpl(this, iter);
    }

    method Erase(mid: UnorderedSetIterator) returns (next: UnorderedSetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires mid.Valid()
      requires mid.Parent() == this
      requires mid.HasPeek?()
      requires mid in Iterators()
      ensures Valid()
      ensures Model() == old(Model())-{old(mid.Peek?())}
      ensures |Model()| == old(|Model()|) - 1 // old(mid.Peek?()) in old(Model())

      ensures fresh(next)
      ensures next.Valid() && next.Parent() == this
      ensures next.Traversed() == old(mid.Traversed())
      ensures |next.Traversed()| == old(|mid.Traversed()|)

      ensures Iterators() >= {next}+old(Iterators())
    {
      assert this !in treemap.Repr();
      var mid' := mid as TreeSetIteratorImpl;
      var iter: UnorderedMapIterator := treemap.Erase(mid'.iter);
      next := new TreeSetIteratorImpl(this, iter);
    }
  }
}
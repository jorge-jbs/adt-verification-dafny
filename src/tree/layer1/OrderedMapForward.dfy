include "../../../src/tree/KeyValue.dfy"
include "../../../src/tree/layer1/UnorderedMap.dfy"
include "../../../src/tree/layer1/OrderedSetUtils.dfy"

module OrderedMapForwardSpec {
  import opened KeyValue
  import opened UnorderedMapSpec
  import opened OrderedSetUtils

  trait {:termination false} OrderedMapForwardIterator extends UnorderedMapIterator {
    function Parent(): UnorderedMap
      reads this

    predicate Valid()
      reads this, Parent(), Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()

    function Index(): int
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures 0 <= Index() <= |Parent().Model()|

    function Traversed(): set<K>
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures Traversed() <= (Parent().Model().Keys)
      ensures 0 <= |Traversed()| <= |Parent().Model().Keys|
      ensures |Traversed()| == Index()
      ensures 0 <= Index() < |Parent().Model()| ==> Traversed() < Parent().Model().Keys && |Traversed()| < |Parent().Model().Keys|
    {
      if Index() == |Parent().Model()| then
        Parent().Model().Keys
      else
        lelemth(Parent().Model().Keys,Index());
        smaller(Parent().Model().Keys, elemth(Parent().Model().Keys, Index()))
    }
    //ensures forall x,y | x in Traversed() && y in Parent().Model().Keys-Traversed() :: x < y

    function Peek?(): (K, V)
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Peek?() in Parent().Model().Items
      ensures key(Peek?()) in Parent().Model() - Traversed()
    {
      assert |Traversed()| == Index() < |Parent().Model()|;
      //assert Traversed() < Parent().Model();
      elemthSet(Parent().Model().Keys,Traversed());
      //elemthSmallerAll(Parent().Model(),Traversed());
      //elemthBiggerAll(Parent().Model(),Traversed());
      var k := elemth(Parent().Model().Keys, Index());
      (k, Parent().Model()[k])
    }

    predicate HasPeek?()
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures HasPeek?()  ==> Traversed() < Parent().Model().Keys && |Traversed()| < |Parent().Model().Keys|
      //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
      ensures !HasPeek?() ==> Traversed() == Parent().Model().Keys && |Traversed()| == |Parent().Model().Keys|
    {
      0 <= Index() < |Parent().Model()|
    }

    method HasPeek() returns (b:bool)
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

      ensures Index() == old(Index())//NEW

      ensures Traversed() == old(Traversed())
      ensures |Traversed()| == old(|Traversed()|)

      ensures old(HasPeek?()) ==> HasPeek?() && Peek?()==old(Peek?())
      ensures b == HasPeek?()

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) :: //NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()) )

    method Peek() returns (p:(K,V))
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

      ensures Index() == old(Index()) //NEW

      ensures Traversed() == old(Traversed()) && Peek?()==old(Peek?())
      ensures |Traversed()| == old(|Traversed()|)

      ensures p == Peek?()
      ensures HasPeek?() && Peek?()==old(Peek?()) // no debería ser necesario pero lo es

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()):://NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()))

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


      ensures Traversed() == {key(old(Peek?()))} + old(Traversed())
      ensures |Traversed()| == 1 + old(|Traversed()|)
      ensures Index() == old(Index()) + 1 //NEW

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && (it != this ==> it.Traversed() == old(it.Traversed())
                                   && |it.Traversed()| == old(|it.Traversed()|)
                                   && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?())))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) && it != this:://NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()))

    method Copy() returns (it: UnorderedMapIterator)
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

      ensures Index() == old(Index()) //NEW

      ensures Traversed() == old(Traversed())
      ensures |Traversed()| == old(|Traversed()|)

      ensures old(HasPeek?()) ==> HasPeek?() && Peek?()==old(Peek?())

      ensures fresh(it)
      ensures it.Valid()
      ensures Parent() == it.Parent()
      ensures it is OrderedMapForwardIterator
      ensures  (it as OrderedMapForwardIterator).Index() == Index()
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

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) :: //NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()) )
  }

  trait {:termination false} OrderedMapForward extends UnorderedMap {
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

      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()))

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

      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()))

    function Iterators(): set<UnorderedMapIterator>
      reads this, Repr()
      requires Valid()
      ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
      ensures forall it | it in Iterators() :: it is OrderedMapForwardIterator

    method First() returns (it: UnorderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures it is OrderedMapForwardIterator
      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures it.Traversed() == {}

      ensures (it as OrderedMapForwardIterator).Index() == 0

      ensures Iterators() >= {it} + old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()))

    method Contains(k: K) returns (b: bool)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures b == (k in Model())

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()):://NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()))

    method At(k: K) returns (v: V)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires k in Model()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures v == Model()[k]

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()):://NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()))

    method Find(k: K) returns (newt: UnorderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures newt is OrderedMapForwardIterator
      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent()==this
      ensures k in old(Model()) ==> newt.HasPeek?() && key(newt.Peek?()) == k
      ensures k !in old(Model()) ==> newt.Traversed() == Model().Keys && |newt.Traversed()| == |Model().Keys|

      ensures k in old(Model()) ==> (newt as OrderedMapForwardIterator).Index() == |smaller(Model().Keys,k)| //NEW
      ensures k !in old(Model()) ==> (newt as OrderedMapForwardIterator).Index() == |Model().Keys|

      ensures Iterators() >= {newt}+old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid())::
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()))

    method Insert(mid: UnorderedMapIterator, k: K, v : V) returns (newt:UnorderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())[k:=v]
      ensures if (k in old(Model())) then |Model()| == old(|Model()|) else |Model()| == 1 + old(|Model()|)

      requires mid.Valid()
      requires mid.Parent() == this
      requires mid in Iterators()

      ensures newt is OrderedMapForwardIterator
      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent() == this
      ensures newt.HasPeek?() && newt.Peek?() == (k,v)

      ensures (newt as OrderedMapForwardIterator).Index() ==  |smaller(Model().Keys,k)|//NEW

      ensures Iterators() >= {newt}+old(Iterators())
    //points either to the inserted elemento or to the already existing one

    method Erase(mid:UnorderedMapIterator) returns (next: UnorderedMapIterator)
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
      ensures Model()== old(Model())- {key(old(mid.Peek?()))} //map k | k in old(Model()) && k != key(old(mid.Peek?()))::old(Model())[k]
      ensures |Model()|==|old(Model())|-1

      ensures next is OrderedMapForwardIterator
      ensures fresh(next)
      ensures next.Valid() && next.Parent() == this
      ensures next.Traversed() == old(mid.Traversed())
      ensures |next.Traversed()| == old(|mid.Traversed()|)

      ensures mid is OrderedMapForwardIterator && (next as OrderedMapForwardIterator).Index() == old((mid as OrderedMapForwardIterator).Index())

      ensures Iterators() >= {next}+old(Iterators())
  }
}

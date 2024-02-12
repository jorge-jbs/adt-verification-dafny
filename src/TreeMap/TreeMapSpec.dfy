include "../../src/Collections/KeyValue.dfy"
include "../../src/UnorderedMap/UnorderedMapSpec.dfy"
include "../../src/OrderedMap/OrderedMapSpec.dfy"
include "../../src/Collections/OrderedSetUtils.dfy"

module TreeMapSpec {
  import opened KeyValue
  import opened UnorderedMapSpec
  import opened OrderedMapSpec
  import opened OrderedSetUtils

  trait {:termination false} TreeMap extends OrderedMap {
/*
    ghost function Iterators(): set<UnorderedMapIterator>
      reads this, Repr()
      requires Valid()
      ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
      ensures forall it | it in Iterators() :: it is OrderedMapIterator

    lemma ApplyForall<A>(x: A, S: set<A>, P: A -> bool)
      requires forall y <- S :: P(y)
      requires x in S
      ensures P(x)
    {}

    twostate lemma ApplyForallAdd(it: UnorderedMapIterator)
      requires old(allocated(it))
      requires old(Valid())
      requires it in old(Iterators())
      requires forall it | it in old(Iterators()) :: it is OrderedMapIterator
      ensures it is OrderedMapIterator
    {
      assert forall it | it in old(Iterators()) :: it is OrderedMapIterator;
      assert it in old(Iterators());
      assume Valid();
      assume it in Iterators();
      assert it is UnorderedMapIterator;
      //ApplyForall(it, old(Iterators()), x => x is OrderedMapIterator);
      assert (it as object) is OrderedMapIterator;
    }
      */

    method Add(k: K,v: V)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())[k:=v]
      ensures if (k in old(Model())) then |Model()| == old(|Model()|)
              else |Model()| == 1 + old(|Model()|)

      ensures Iterators() >= old(Iterators())

      //specific invalidation policy
      ensures forall it: OrderedMapIterator <- old(Iterators()) | old(it.Valid()) ::
        && var it' := Cast(it);
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && (it.HasPeek?() <==> old(it.HasPeek?()))
        && (
          it.HasPeek?() && (k !in old(Model()) || k != old(it.Peek?().0)) ==>
            it.Peek?() == old(it.Peek?())
        )
        && ( //value update
          it.HasPeek?() && k in old(Model()) && k == old(it.Peek?().0) ==>
            it.Peek?() == (k,v)
        )
        && (
          if k in old(Model()) || it'.Index() == -1 || (it.HasPeek?() && it.Peek?().0 < k) then
            it'.Index() == old(it'.Index())
          else
            it'.Index() == old(it'.Index()) + 1
        )
        && (
          if k in old(Model()) || (it.HasPeek?() && it.Peek?().0 < k) then
            && it.Traversed() == old(it.Traversed())
            && |it.Traversed()| == |old(it.Traversed())|
          else
            && it.Traversed() == old(it.Traversed()) + {k}
            && |it.Traversed()| == |old(it.Traversed())| + 1
        )

    method Remove(k: K)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model()) - {k}
      ensures if (k in old(Model())) then |Model()| == old(|Model()|) - 1
              else |Model()| == old(|Model()|)

      ensures Iterators() >= old(Iterators())
      
      //specific invalidation policy
      ensures
          forall it: OrderedMapIterator <- old(Iterators()) | 
            && old(it.Valid())
            && (old(it.HasPeek?()) ==> old(it.Peek?().0) != k)
          :: it.Valid()
          && it.Parent() == old(it.Parent())
          && (it.HasPeek?() <==> old(it.HasPeek?()))
          && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
          && var it' := Cast(it);
          && (           
            if k !in old(Model()) || it'.Index() == -1 || (it.HasPeek?() && it.Peek?().0 < k) then
              it'.Index() == old(it'.Index())
            else
              it'.Index() == old(it'.Index()) - 1
            )
          && (
            if k !in old(Model()) || (it.HasPeek?() && it.Peek?().0 < k) then
                && it'.Traversed() == old(it'.Traversed())
                && |it'.Traversed()| == |old(it'.Traversed())|
            else
                && it'.Traversed() == old(it'.Traversed()) - {k}
                && |it'.Traversed()| == |old(it'.Traversed())| - 1
          )

    method Insert(mid: UnorderedMapIterator, k: K, v : V) returns (newt: UnorderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())[k:=v]
      ensures if (k in old(Model())) then |Model()| == old(|Model()|)
              else |Model()| == 1 + old(|Model()|)

      requires mid.Valid()
      requires mid.Parent() == this
      requires mid in Iterators()

      ensures newt is OrderedMapIterator
      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent() == this
      ensures newt.HasPeek?() && newt.Peek?() == (k,v)

      ensures (newt as OrderedMapIterator).Index() ==  |smaller(Model().Keys,k)|//NEW

      ensures Iterators() >= {newt}+old(Iterators())

      //specific invalidation policy
      //mid is like the rest of iterators
      ensures forall it: OrderedMapIterator <- old(Iterators()) | old(it.Valid()) ::
        && var it' := Cast(it);
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && (it.HasPeek?() <==> old(it.HasPeek?()))
        && (
          it.HasPeek?() && (k !in old(Model()) || k != it.Peek?().0) ==>
            it.Peek?() == old(it.Peek?())
        )
        && ( //value update
          it.HasPeek?() && k in old(Model()) && k == old(it.Peek?().0) ==>
            it.Peek?() == (k,v)
        )
        && (
          if k in old(Model()) || it'.Index() == -1 || (it.HasPeek?() && it.Peek?().0 < k) then
            it'.Index() == old(it'.Index())
          else
            it'.Index() == old(it'.Index()) + 1
        )
        && (
          if k in old(Model()) || (it.HasPeek?() && it.Peek?().0 < k) then
            && it.Traversed() == old(it.Traversed())
            && |it.Traversed()| == |old(it.Traversed())|
          else
            && it.Traversed() == old(it.Traversed()) + {k}
            && |it.Traversed()| == |old(it.Traversed())| + 1
        )

    method Erase(mid: UnorderedMapIterator) returns (next: UnorderedMapIterator)
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

      ensures next is OrderedMapIterator
      ensures fresh(next)
      ensures next.Valid() && next.Parent() == this
      ensures next.Traversed() == old(mid.Traversed())
      ensures |next.Traversed()| == old(|mid.Traversed()|)

      ensures mid is OrderedMapIterator && (next as OrderedMapIterator).Index() == old((mid as OrderedMapIterator).Index())

      ensures Iterators() >= {next}+old(Iterators())
      
      //specific invalidation policy
      ensures
        var k := old(mid.Peek?().0);
       forall it: OrderedMapIterator <- old(Iterators()) | 
            && old(it.Valid())
            && (old(it.HasPeek?()) ==> old(it.Peek?().0) != k)
          :: it.Valid()
          && it.Parent() == old(it.Parent())
          && (it.HasPeek?() <==> old(it.HasPeek?()))
          && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
          && var it' := Cast(it);
          && (
            if k !in old(Model()) || it'.Index() == -1 || (it.HasPeek?() && it.Peek?().0 < k) then
              it'.Index() == old(it'.Index())
            else
              it'.Index() == old(it'.Index()) - 1
          )
          && (
            if k !in old(Model()) || (it.HasPeek?() && it.Peek?().0 < k) then
                && it'.Traversed() == old(it'.Traversed())
                && |it'.Traversed()| == |old(it'.Traversed())|
            else
                && it'.Traversed() == old(it'.Traversed()) - {k}
                && |it'.Traversed()| == |old(it'.Traversed())| - 1
         )
  }
}

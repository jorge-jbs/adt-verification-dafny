include "../Collections/Seq.dfy"
include "../Collections/KeyValue.dfy"
include "../UnorderedSet/UnorderedSetSpec.dfy"
include "../OrderedSet/OrderedSetSpec.dfy"
include "../Collections/OrderedSetUtils.dfy"

module TreeSetSpec {
  import opened Seq
  import opened KeyValue
  import opened UnorderedSetSpec
  import opened OrderedSetSpec
  import opened OrderedSetUtils

  trait {:termination false} TreeSet extends OrderedSet {
    method Add(x:K)
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

      //specific invalidation policy
      ensures forall it: OrderedSetIterator <- old(Iterators()) | old(it.Valid()) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && (it.HasPeek?() <==> old(it.HasPeek?()))
        && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
        && (
          if x in old(Model()) || it.Index() == -1 || (it.HasPeek?() && it.Peek?() < x) then
            it.Index() == old(it.Index())
          else
            it.Index() == old(it.Index()) + 1
        )
        && (
          if x in old(Model()) || (it.HasPeek?() && it.Peek?() < x) then
            && it.Traversed() == old(it.Traversed())
            && |it.Traversed()| == |old(it.Traversed())|
          else
            && it.Traversed() == old(it.Traversed()) + {x}
            && |it.Traversed()| == |old(it.Traversed())| + 1
        )

    method Remove(x:K)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model()) - {x}
      ensures if (x in old(Model())) then
                |Model()| == old(|Model()|) - 1
              else
                |Model()| == old(|Model()|)

      ensures Iterators() >= old(Iterators())

      //specific invalidation policy
      ensures forall it: OrderedSetIterator <- old(Iterators()) | 
            && old(it.Valid())
            && (old(it.HasPeek?()) ==> old(it.Peek?()) != x) ::
          && it.Valid()
          && it.Parent() == old(it.Parent())
          && (it.HasPeek?() <==> old(it.HasPeek?()))
          && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
          && var it' := Cast(it);
          && (
            if x !in old(Model()) || it'.Index() == -1 || (it.HasPeek?() && it.Peek?() < x) then
              it'.Index() == old(it'.Index())
            else
              it'.Index() == old(it'.Index()) - 1
          )
          && (
            if x !in old(Model()) || (it.HasPeek?() && it.Peek?() < x) then
                && it'.Traversed() == old(it'.Traversed())
                && |it'.Traversed()| == |old(it'.Traversed())|
            else
                && it'.Traversed() == old(it'.Traversed()) - {x}
                && |it'.Traversed()| == |old(it'.Traversed())| - 1
          )

    method Insert(mid: UnorderedSetIterator, x: K) returns (newt:UnorderedSetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model()) + {x}
      ensures if (x in old(Model())) then |Model()| == old(|Model()|) else |Model()| == 1 + old(|Model()|)

      requires mid.Valid()
      //mid just a hint, it is inserted where corresponds
      //efficiently or not if it respects order
      requires mid.Parent() == this
      requires mid in Iterators()

      ensures newt is OrderedSetIterator
      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent() == this
      ensures newt.HasPeek?() && newt.Peek?() == x

      ensures (newt as OrderedSetIterator).Index() ==  |smaller(Model(),x)|//NEW

      ensures Iterators() >= {newt} + old(Iterators())

      //specific invalidation policy
      //mid is like the rest of iterators
      ensures forall it: OrderedSetIterator <- old(Iterators()) | old(it.Valid()) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && (it.HasPeek?() <==> old(it.HasPeek?()))
        && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
        && (
          if x in old(Model()) || it.Index() == -1 || (it.HasPeek?() && it.Peek?() < x) then
            it.Index() == old(it.Index())
          else
            it.Index() == old(it.Index()) + 1
        )
        && (
          if x in old(Model()) || (it.HasPeek?() && it.Peek?() < x) then
            && it.Traversed() == old(it.Traversed())
            && |it.Traversed()| == |old(it.Traversed())|
          else
            && it.Traversed() == old(it.Traversed()) + {x}
            && |it.Traversed()| == |old(it.Traversed())| + 1
        )

    method Erase(mid:UnorderedSetIterator) returns (next: UnorderedSetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()

      requires mid.Valid()
      requires mid.Parent() == this
      requires mid.HasPeek?()
      requires mid in Iterators()

      ensures Valid()
      ensures Model()== old(Model())-{old(mid.Peek?())}
      ensures |Model()| == old(|Model()|) - 1

      ensures next is OrderedSetIterator
      ensures fresh(next)
      ensures next.Valid() && next.Parent()==this
      ensures next.Traversed()==old(mid.Traversed())
      ensures |next.Traversed()| == old(|mid.Traversed()|)

      ensures mid is OrderedSetIterator && (next as OrderedSetIterator).Index() == old((mid as OrderedSetIterator).Index())

      ensures Iterators() >= {next}+old(Iterators())
      ensures Iterators() >= {next} + old(Iterators())
      ensures
        var x := old(mid.Peek?());
        forall it: OrderedSetIterator <- old(Iterators()) | 
            && old(it.Valid())
            && (old(it.HasPeek?()) ==> old(it.Peek?()) != x) ::
          && it.Valid()
          && it.Parent() == old(it.Parent())
          && (it.HasPeek?() <==> old(it.HasPeek?()))
          && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
          && (
            if (it.HasPeek?() ==> it.Peek?() < x) && old(it.Index()) != old(|Model()|) then
              it.Index() == old(it.Index())
            else
              it.Index() == old(it.Index()) - 1
          )
          && (
            if it.HasPeek?() && it.Peek?() < x then
              && it.Traversed() == old(it.Traversed())
              && |it.Traversed()| == |old(it.Traversed())|
            else
              && it.Traversed() == old(it.Traversed()) - {x}
              && |it.Traversed()| == |old(it.Traversed())| - 1
          )
  }

  method {:verify false} {:timeLimitMultiplier 100} try(s:TreeSet)
    modifies s, s.Repr()
    requires s.Valid() && s.Empty?()
    requires allocated(s.Repr())
    ensures s.Valid()
    ensures fresh(s.Repr()-old(s.Repr()))
    ensures  allocated(s.Repr())
  {
    s.Add(2); s.Add(7); s.Add(0); s.Add(1);s.Add(10);
    assert s.Model()=={0,1,2,7,10};
    var it0 := s.First();
    var itn := s.Last();
    var it1 := s.Find(1);
    assert it1 is OrderedSetIterator;
    assert it0 is OrderedSetIterator;
    assert itn is OrderedSetIterator;

    var it2 := s.Find(2);
    assert it2 is OrderedSetIterator;

    assume it1.Index() == 1;
    assume it2.Index() == 2;

    s.Remove(1);
    assert it2.Index() == 1;
    //assert it1.Index() == 1; //no puede demostrarlo
    assert it0.Index() == 0;
    assert itn.Index() == 3;
  }
}
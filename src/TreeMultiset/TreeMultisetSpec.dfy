include "../Collections/Seq.dfy"
include "../Collections/KeyValue.dfy"
include "../UnorderedMultiset/UnorderedMultisetSpec.dfy"
include "../OrderedMultiset/OrderedMultisetSpec.dfy"
include "../Collections/OrderedMultisetUtils.dfy"

module TreeMultisetSpec {
  import opened Seq
  import opened KeyValue
  import opened UnorderedMultisetSpec
  import opened OrderedMultisetSpec
  import opened OrderedMultisetUtils

  
  trait {:termination false} TreeMultiset extends OrderedMultiset {


    method Add(x:K)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model()) + multiset{x}
      ensures |Model()| == 1 + old(|Model()|)

      ensures Iterators() >= old(Iterators())

      ensures forall it <- old(Iterators()) | old(it.Valid())
        :: it is OrderedMultisetIterator
        && var it' := it as OrderedMultisetIterator;
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && (it.HasPeek?() <==> old(it.HasPeek?()))
        && (it.HasPeek?()  ==> it.Peek?() == old(it.Peek?()))
        && (
          if it'.Index() == -1 || (it.HasPeek?() && it.Peek?() < x) then    // insert at the beginning of equal elements
          //if it'.Index() == -1 || (it.HasPeek?() && it.Peek?() <= x) then //another option:insert at the end

            it'.Index() == old(it'.Index()) 
          else
            it'.Index() == old(it'.Index()) + 1
        )
        && (
          if (it.HasPeek?() && it.Peek?() < x) then
          // if (it.HasPeek?() && it.Peek?() <= x) then //another option, insert at the end

            && it.Traversed() == old(it.Traversed())
            && |it.Traversed()| == |old(it.Traversed())|
          else
            && it.Traversed() == old(it.Traversed()) + multiset{x}
            && |it.Traversed()| == |old(it.Traversed())| + 1
        )

    method Remove(x:K)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model()) - multiset{x}
      ensures if (x in old(Model())) then 
                |Model()| == old(|Model()|) - 1
              else 
                |Model()| == old(|Model()|)

      ensures Iterators() >= old(Iterators())
      
      ensures
        forall it | it in old(Iterators())
            && old(it.Valid())
            && (old(it.HasPeek?()) ==> old(it.Peek?()) != x)
          :: it is OrderedMultisetIterator
          && it.Valid()
          && it.Parent() == old(it.Parent())
          && (it.HasPeek?() <==> old(it.HasPeek?()))
          && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
          && var it' := it as OrderedMultisetIterator;
          && (
            if x in old(Model()) && ((it.HasPeek?() && x < it.Peek?()) || old(it'.Index()) == old(|Model()|)) then
              it'.Index() == old(it'.Index()) - 1
            else
              it'.Index() == old(it'.Index())
          )
          && (
            if x in old(Model()) && (it.HasPeek?() ==> x < it.Peek?()) then
              && it'.Traversed() == old(it'.Traversed()) - multiset{x}
              && |it'.Traversed()| == |old(it'.Traversed())| - 1
            else
              && it'.Traversed() == old(it'.Traversed())
              && |it'.Traversed()| == |old(it'.Traversed())|
          )

      ensures
          forall it | it in old(Iterators())
            && old(it.Valid())
            && old(it.HasPeek?()) 
            && old(it.Peek?()) == x 
            && it is OrderedMultisetIterator
            && var it' := it as OrderedMultisetIterator;
            && var ssmaller := |msmaller(old(Model()),x)|;
            && x in old(Model())  ==> old(it'.Index()) !=  ssmaller
            //we remove the first appearance
            ::  
          && it.Valid()
          && it.Parent() == old(it.Parent())
          && (it.HasPeek?() <==> old(it.HasPeek?()))
          && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
          && var it' := it as OrderedMultisetIterator;
          && var ssmaller := |msmaller(old(Model()),x)|;
            (
              if x in old(Model()) && old(it'.Index()) > ssmaller then
                it'.Index() == old(it'.Index()) - 1
              else
                it'.Index() == old(it'.Index())
            )
          && 
            ( 
              if x in old(Model()) && (old(it'.Index()) > ssmaller || old(it'.Index()) == -1) then
                && it'.Traversed() == old(it'.Traversed()) - multiset{x}
                && |it'.Traversed()| == |old(it'.Traversed())| - 1
              else
                && it'.Traversed() == old(it'.Traversed())
                && |it'.Traversed()| == |old(it'.Traversed())|
            )

               
    //insertion after the strictly smaller elements
    method Insert(mid: UnorderedMultisetIterator, x: K) returns (newt:UnorderedMultisetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model()) + multiset{x}
      ensures |Model()| == 1 + old(|Model()|)

      requires mid.Valid()
      //mid just a hint, it is inserted where corresponds
      //efficiently or not if it respects order
      requires mid.Parent() == this
      requires mid in Iterators()

      ensures newt is OrderedMultisetIterator
      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent() == this
      ensures newt.HasPeek?() && newt.Peek?() == x

      ensures (newt as OrderedMultisetIterator).Index() ==  |msmaller(Model(),x)|//NEW

      ensures Iterators() >= {newt} + old(Iterators())

      //specific invalidation policy
      ensures forall it <- old(Iterators()) | old(it.Valid())  
        :: it is OrderedMultisetIterator
        && var it' := it as OrderedMultisetIterator;
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && (it.HasPeek?() <==> old(it.HasPeek?()))
        && (it.HasPeek?()  ==> it.Peek?() == old(it.Peek?()))
        && (
          if it'.Index() == -1 || (it.HasPeek?() && it.Peek?() < x) then
          //if it'.Index() == -1 || (it.HasPeek?() && it.Peek?() <= x) then  // another option, insert after equal elements

            it'.Index() == old(it'.Index())
          else
            it'.Index() == old(it'.Index()) + 1
        )
        && (
          if(it.HasPeek?() && it.Peek?() < x) then
          //if(it.HasPeek?() && it.Peek?() <= x) then //another option, insert at the end

            && it.Traversed() == old(it.Traversed())
            && |it.Traversed()| == |old(it.Traversed())|
          else
            && it.Traversed() == old(it.Traversed()) + multiset{x}
            && |it.Traversed()| == |old(it.Traversed())| + 1
        )

    method Erase(mid:UnorderedMultisetIterator) returns (next: UnorderedMultisetIterator)
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
      ensures Model()== old(Model()) -  multiset{old(mid.Peek?())}
      ensures |Model()| == old(|Model()|) - 1

      ensures next is OrderedMultisetIterator
      ensures fresh(next)
      ensures next.Valid() && next.Parent()==this
      ensures next.Traversed()==old(mid.Traversed())      
      ensures |next.Traversed()| == old(|mid.Traversed()|)

      ensures mid is OrderedMultisetIterator && (next as OrderedMultisetIterator).Index() == old((mid as OrderedMultisetIterator).Index())

      ensures Iterators() >= {next}+old(Iterators())

      ensures
        var x := old(mid.Peek?());
        var mid' := old((mid as OrderedMultisetIterator).Index());
        forall it | it in old(Iterators())
            && old(it.Valid())
            && it is OrderedMultisetIterator
            && var it' := it as OrderedMultisetIterator;
            //&& (old(it.HasPeek?()) ==> old(it.Peek?()) != x)
            && mid' != old(it'.Index())
          :: it is OrderedMultisetIterator
          && it.Valid()
          && it.Parent() == old(it.Parent())
          && (it.HasPeek?() <==> old(it.HasPeek?()))
          && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
          && var it' := it as OrderedMultisetIterator;
          && (
            if mid' < old(it'.Index()) then
              it'.Index() == old(it'.Index()) - 1
            else
              it'.Index() == old(it'.Index()) 
          )
          && (
            if mid' < old(it'.Index()) || old(it'.Index()) == -1 then
              && it'.Traversed() == old(it'.Traversed()) - multiset{x}
              && |it'.Traversed()| == |old(it'.Traversed())| - 1
            else
              && it'.Traversed() == old(it'.Traversed())
              && |it'.Traversed()| == |old(it'.Traversed())|
          )

  }



  method {:verify false} {:timeLimitMultiplier 100} try(s:TreeMultiset)
    modifies s, s.Repr()
    requires s.Valid() && s.Empty?()
    requires allocated(s.Repr())
    ensures s.Valid()
    ensures fresh(s.Repr()-old(s.Repr()))
    ensures  allocated(s.Repr())
  {


  /*  s.Add(2); s.Add(7); s.Add(0); s.Add(1);s.Add(10);
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
   assert itn.Index() == 3;*/
   }
}
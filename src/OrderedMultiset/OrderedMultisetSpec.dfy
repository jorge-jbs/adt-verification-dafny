include "../UnorderedMultiset/UnorderedMultisetSpec.dfy"
include "../Collections/OrderedMultisetUtils.dfy"

module OrderedMultisetSpec {
  import opened KeyValue
  import opened UnorderedMultisetSpec
  import opened OrderedMultisetUtils

  trait {:termination false} OrderedMultisetIterator extends UnorderedMultisetIterator {
    ghost function Parent(): UnorderedMultiset
      reads this
      ensures Parent() is OrderedMultiset

    ghost predicate Valid()
      reads this, Parent(), Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()

    ghost function Index(): int
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures -1 <= Index() <= |Parent().Model()|

    ghost function Traversed():multiset<int>
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures Traversed() <= Parent().Model()
      ensures 0 <= |Traversed()| <= |Parent().Model()|
      ensures Index() >= 0 <==> |Traversed()| == Index()
      ensures 0 <= Index() < |Parent().Model()| ==> Traversed() < Parent().Model() && |Traversed()| < |Parent().Model()|
    {
      if (Index() == -1 || Index() == |Parent().Model()|) then Parent().Model()
      else
        lelemth(Parent().Model(),Index());
        var p := elemth(Parent().Model(),Index());
        var sm :=  msmaller(Parent().Model(),p);
        sm[p := Index()-|sm|]

    }
    //Several elements equal to the Peek may be in Traversed and some others not
    // Example: Model=={1,1,2,3,3,3,4,5} Traversed=={1,1,2,3,3} Peek=3
    ghost predicate HasPeek?()
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures HasPeek?() <==> Traversed() < Parent().Model() &&  |Traversed()| < |Parent().Model()|
      ensures !HasPeek?() ==> Traversed() == Parent().Model() && |Traversed()| == |Parent().Model()|
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
                (it is OrderedMultisetIterator &&
                 (it as OrderedMultisetIterator).Index() == old((it as OrderedMultisetIterator).Index()) )

    ghost function Peek?():int
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Peek?() in Parent().Model()
      ensures Peek?() in Parent().Model()-Traversed()//&& (Parent().Model()-Traversed())[Peek?()]>0
    {
      lelemth(Parent().Model(),Index());
      //assert Traversed()[elemth(Parent().Model(),Index())] == Index()-|msmaller(Parent().Model(),elemth(Parent().Model(),Index()))|;
      //assert (Parent().Model()-Traversed())[elemth(Parent().Model(),Index())] == Parent().Model()[elemth(Parent().Model(),Index())]-Traversed()[elemth(Parent().Model(),Index())];
      //assert Parent().Model()[elemth(Parent().Model(),Index())] > Traversed()[elemth(Parent().Model(),Index())];
      elemth(Parent().Model(),Index())}


    method Peek() returns (p:int)
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

      ensures Traversed() == old(Traversed())
      ensures |Traversed()| == old(|Traversed()|)
      ensures HasPeek?() && Peek?()==old(Peek?()) // no debería ser necesario pero lo es
      ensures p == Peek?()

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) :: //NEW
                (it is OrderedMultisetIterator &&
                 (it as OrderedMultisetIterator).Index() == old((it as OrderedMultisetIterator).Index()) )


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
      ensures Traversed() == multiset{old(Peek?())}+old(Traversed())
      ensures |Traversed()| == 1 + |old(Traversed())|

      ensures Index() == old(Index()) + 1 //NEW

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && (it != this ==> it.Traversed() == old(it.Traversed())
                                   && |it.Traversed()| == old(|it.Traversed()|)                                                  && |it.Traversed()| == old(|it.Traversed()|)
                                   && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?())))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) &&  it != this:://NEW
                (it is OrderedMultisetIterator &&
                 (it as OrderedMultisetIterator).Index() == old((it as OrderedMultisetIterator).Index()) )

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

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) &&  it != this:://NEW
                (it is OrderedMultisetIterator &&
                 (it as OrderedMultisetIterator).Index() == old((it as OrderedMultisetIterator).Index()) )

    method Copy() returns (it: UnorderedMultisetIterator)
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

      ensures Index() == old(Index()) //NEW

      ensures Traversed() == old(Traversed())
      ensures |Traversed()| == old(|Traversed()|)
      ensures old(HasPeek?()) ==> HasPeek?() && Peek?()==old(Peek?())

      ensures it.Valid()
      ensures Parent() == it.Parent()
      ensures it is OrderedMultisetIterator
      ensures  (it as OrderedMultisetIterator).Index() == Index()
      ensures Traversed() == it.Traversed()
      ensures HasPeek?() ==> it.HasPeek?() && Peek?()==it.Peek?()

      ensures Parent().Iterators() >= {it} + old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) :: //NEW
                (it is OrderedMultisetIterator &&
                 (it as OrderedMultisetIterator).Index() == old((it as OrderedMultisetIterator).Index()) )
  }

  trait {:termination false} OrderedMultiset extends UnorderedMultiset {
    //Novelties respect UnorderedSet
    // Last iterator method
    // Find knows the traversed elements
    // Insert knows the traversed elements
    // Those methods that return iterators do return OrderedSetIterator
    // Methods receiving iterators may be called with OrderedSetIterator
    // The rest remains the same
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
                (it is OrderedMultisetIterator &&
                 (it as OrderedMultisetIterator).Index() == old((it as OrderedMultisetIterator).Index()))

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
                (it is OrderedMultisetIterator &&
                 (it as OrderedMultisetIterator).Index() == old((it as OrderedMultisetIterator).Index()))

    ghost function Iterators(): set<UnorderedMultisetIterator>
      reads this, Repr()
      requires Valid()
      ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
      ensures forall it | it in Iterators() :: it is OrderedMultisetIterator

    method First() returns (it: UnorderedMultisetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures it is OrderedMultisetIterator
      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures it.Traversed()==multiset{}
      ensures (it as OrderedMultisetIterator).Index() == 0

      ensures Iterators() >= {it} + old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
                (it is OrderedMultisetIterator &&
                 (it as OrderedMultisetIterator).Index() == old((it as OrderedMultisetIterator).Index()))


    method Last() returns (it: OrderedMultisetIterator)//iterator to the last element
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures it is OrderedMultisetIterator
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

      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
                (it is OrderedMultisetIterator &&
                 (it as OrderedMultisetIterator).Index() == old((it as OrderedMultisetIterator).Index()))

    method Contains(x:K) returns (b:bool)
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

      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
                (it is OrderedMultisetIterator &&
                 (it as OrderedMultisetIterator).Index() == old((it as OrderedMultisetIterator).Index()))

    method Count(x:K) returns (c:int)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures c == Model()[x]

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
                (it is OrderedMultisetIterator &&
                 (it as OrderedMultisetIterator).Index() == old((it as OrderedMultisetIterator).Index()))

    method Find(x:K) returns (newt:UnorderedMultisetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures newt is OrderedMultisetIterator
      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent()==this
      ensures x in old(Model()) ==> newt.HasPeek?() && newt.Peek?() == x
      ensures x !in old(Model()) ==> newt.Traversed() == Model() && |newt.Traversed()| == |Model()|

      ensures x in old(Model()) ==> (newt as OrderedMultisetIterator).Index() == |msmaller(Model(),x)| //NEW
      ensures x !in old(Model()) ==> (newt as OrderedMultisetIterator).Index() == |Model()|

      ensures Iterators() >= {newt}+old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
                (it is OrderedMultisetIterator &&
                 (it as OrderedMultisetIterator).Index() == old((it as OrderedMultisetIterator).Index()))

    //Add, Remove and RemoveAll are the same

    method Insert(mid: UnorderedMultisetIterator, x: int) returns (newt:UnorderedMultisetIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model()) + multiset{x}
      ensures |Model()| == 1 + old(|Model()|)
      //mid just a hint, it is inserted where corresponds
      //efficiently or not if it respects order

      requires mid.Valid()
      requires mid.Parent() == this
      requires mid in Iterators()

      ensures newt is OrderedMultisetIterator
      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent()==this
      ensures newt.HasPeek?() &&
              msmaller(Model(),x) <= newt.Traversed() <= msmaller(Model(),x)[x:=old(Model()[x])] &&
              newt.Peek?()==x

      ensures Iterators() >= {newt}+old(Iterators())
    //Example: 1,2,2,2,2,3 insert another 2 , Traversed may be
    //{1} (newt points to the first 2), {1,2}, ..., {1,2,2,2,2} (newt points to the last 2)

    //points either to the inserted elemento or to the already existing one

    method Erase(mid:UnorderedMultisetIterator) returns (next: UnorderedMultisetIterator)
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

      ensures Model()== old(Model())-multiset{old(mid.Peek?())}
      ensures |Model()| == old(|Model()|) - 1 // old(mid.Peek?()) in old(Model())

      ensures next is OrderedMultisetIterator
      ensures fresh(next)
      ensures next.Valid() && next.Parent()==this
      ensures next.Traversed()==old(mid.Traversed())
      ensures |next.Traversed()| == old(|mid.Traversed()|)

      ensures mid is OrderedMultisetIterator && (next as OrderedMultisetIterator).Index() == old((mid as OrderedMultisetIterator).Index())

      ensures Iterators() >= {next}+old(Iterators())
  }



  method {:verify true} try(s:OrderedMultiset)
    modifies s, s.Repr()
    requires s.Valid() && s.Empty?()
    requires forall x | x in s.Repr() :: allocated(x)
    ensures s.Valid()
    ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
    ensures fresh(s.Repr()-old(s.Repr()))
    ensures forall x | x in s.Repr() :: allocated(x)
  {


    s.Add(2); s.Add(7); s.Add(0); s.Add(1);s.Add(10);
    assert s.Model()==multiset{0,1,2,7,10};

    var b:=s.Contains(10);
    assert b;

    var it : OrderedMultisetIterator :=s.First(); var cont:=0;
    var itHasPeek := it.HasPeek();
    while (itHasPeek)
      //decreases |s.Model()|-|it.Traversed()|
      decreases |s.Model()|-it.Index()
      invariant it.Valid() && it.Parent()==s
      invariant s.Valid() && s.Model()==multiset{0,1,2,7,10}
      invariant itHasPeek == it.HasPeek?()
      invariant fresh(s.Repr() - old(s.Repr()))
      invariant allocated(s.Repr())

    {var aux := it.Peek();
     it.Next();
     if (aux%2==0) {cont:=cont+1;}
     itHasPeek := it.HasPeek();
    }
  }
   /*  assert s.Model()=={0,1,2,7,10};
    var it2 :=s.find(2) ;
    assert it2 is OrderedSetIterator;
    assert s is OrderedSet;
    assert 2 in s.Model();
    assert it2.Peek()==2;
    assert it2.Peek()!=5;
    assert (it2 as OrderedSetIterator).Traversed()=={0,1};//OO(
    assert it2.Index()==2;
   it2:=s.find(7); 
    assert it2.Traversed()=={0,1,2};
    assert it2.Index()==3;  
    var aux:=it2.Next();
    assert aux==7;assert it2.Index()==4;
  
    var it3:OrderedSetIterator:=s.find(7);
    it3:=s.insert(it3,5);//efficient
    assert it3.Traversed()=={0,1,2};
    assert it3.Index()==3;
    it3:=s.insert(it3,12);
      assert it3.Traversed()=={0,1,2,5,7,10};
    assert it3.Index()==6;
    //assert maximum(it3.Traversed())==10;
    var z:=it3.Prev();

    var it4:=s.Last();
    z:=it4.Prev();
    z:=it4.Prev();

    assert z==10;
    z:=it4.Prev();
    z:=it4.Prev();
    z:=it4.Prev();
    z:=it4.Prev();
    z:=it4.Prev();
    z:=it4.Prev();
    assert !it4.HasPrev();

  }*/
}

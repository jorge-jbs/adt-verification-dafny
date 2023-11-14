include "../Collections/Seq.dfy"
include "../Collections/KeyValue.dfy"
include "../UnorderedSet/UnorderedSetSpec.dfy"
include "../Collections/OrderedSetUtils.dfy"


module OrderedSetForwardSpec {
  import opened Seq
  import opened KeyValue
  import opened UnorderedSetSpec
  import opened OrderedSetUtils

trait OrderedSetIteratorForward extends UnorderedSetIterator{
  ghost function Parent(): UnorderedSet
    reads this
    ensures Parent() is OrderedSetForward

  ghost predicate Valid()
    reads this, Parent(), Parent().Repr()
    ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()

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
    ensures 0 <= Index() <= |Parent().Model()|


  ghost function Traversed():set<K>
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures Traversed() <= Parent().Model()
    ensures 0 <= |Traversed()| <= |Parent().Model()|
    ensures |Traversed()| == Index()
    ensures Index() < |Parent().Model()| ==> Traversed() < Parent().Model() && |Traversed()| < |Parent().Model()|
  {
    if (Index() == |Parent().Model()|) then Parent().Model()
    else
      lelemth(Parent().Model(),Index());
      smaller(Parent().Model(),elemth(Parent().Model(),Index()))
  }

  ghost function Peek?():K
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasPeek?()
    ensures Peek?() in Parent().Model() && Peek?() !in Traversed()
    /*ensures forall x | x in Traversed() :: x < Peek?()
    ensures forall x | x in Parent().Model()-Traversed()-{Peek?()} :: Peek?() < x
    ensures forall x | x in Parent().Model()-Traversed() :: Peek?() <= x*/
  {
    assert |Traversed()| == Index() < |Parent().Model()|;
    //assert Traversed() < Parent().Model();
    elemthSet(Parent().Model(),Traversed());
    //elemthSmallerAll(Parent().Model(),Traversed());
    //elemthBiggerAll(Parent().Model(),Traversed());

    elemth(Parent().Model(),Index())
  }


  ghost predicate HasPeek?()
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    //ensures HasPeek?() <==> Traversed() < Parent().Model() &&  |Traversed()| < |Parent().Model()|
    ensures HasPeek?() ==> Traversed() < Parent().Model() &&  |Traversed()| < |Parent().Model()|
    /*ensures Traversed() < Parent().Model() ==> HasPeek?() 
    ensures |Traversed()| < |Parent().Model()| ==> HasPeek?()*/
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
              (it is OrderedSetIteratorForward &&
               (it as OrderedSetIteratorForward).Index() == old((it as OrderedSetIteratorForward).Index()) )

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

    ensures Traversed() == {old(Peek?())}+old(Traversed())
    ensures |Traversed()| == 1 + |old(Traversed())|
    ensures Index() == old(Index()) + 1 //NEW

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
              && it.Valid()
              && it.Parent() == old(it.Parent())
              && (it != this ==> it.Traversed() == old(it.Traversed())
                                 && |it.Traversed()| == old(|it.Traversed()|)
                                 && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?())))

    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) && it != this:://NEW
              (it is OrderedSetIteratorForward &&
               (it as OrderedSetIteratorForward).Index() == old((it as OrderedSetIteratorForward).Index()) )

  method Peek() returns (p:K)
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

    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()):://NEW
              (it is OrderedSetIteratorForward &&
               (it as OrderedSetIteratorForward).Index() == old((it as OrderedSetIteratorForward).Index()) )


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

    ensures Index() == old(Index()) //NEW

    ensures Traversed() == old(Traversed())
    ensures |Traversed()| == old(|Traversed()|)

    ensures old(HasPeek?()) ==> HasPeek?() && Peek?()==old(Peek?())


    ensures it.Valid()
    ensures Parent() == it.Parent()

    ensures it is OrderedSetIteratorForward
    ensures  (it as OrderedSetIteratorForward).Index() == Index()
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
              (it is OrderedSetIteratorForward &&
               (it as OrderedSetIteratorForward).Index() == old((it as OrderedSetIteratorForward).Index()) )

}

trait OrderedSetForward extends UnorderedSet{


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
              (it is OrderedSetIteratorForward &&
               (it as OrderedSetIteratorForward).Index() == old((it as OrderedSetIteratorForward).Index()))

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
              (it is OrderedSetIteratorForward &&
               (it as OrderedSetIteratorForward).Index() == old((it as OrderedSetIteratorForward).Index()))


  ghost function Iterators(): set<UnorderedSetIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() ::  it in Repr() && it.Parent() == this
    ensures forall it | it in Iterators() :: it is OrderedSetIteratorForward

  method First() returns (it: UnorderedSetIterator)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures |Model()| == old(|Model()|)

    ensures it is OrderedSetIteratorForward
    ensures fresh(it)
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Traversed() == {}

    ensures (it as OrderedSetIteratorForward).Index() == 0

    ensures Iterators() >= {it} + old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
              && it.Valid()
              && it.Parent() == old(it.Parent())
              && it.Traversed() == old(it.Traversed())
              && |it.Traversed()| == old(|it.Traversed()|)
              && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

    ensures forall it | it in old(Iterators()) && old(it.Valid()):://NEW
              (it is OrderedSetIteratorForward &&
               (it as OrderedSetIteratorForward).Index() == old((it as OrderedSetIteratorForward).Index()) )



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

    ensures forall it | it in old(Iterators()) && old(it.Valid()):://NEW
              (it is OrderedSetIteratorForward &&
               (it as OrderedSetIteratorForward).Index() == old((it as OrderedSetIteratorForward).Index()) )



  //Add and Remove remain the same


  method Find(x:K) returns (newt:UnorderedSetIterator)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures |Model()| == old(|Model()|)

    ensures newt is OrderedSetIteratorForward
    ensures fresh(newt)
    ensures newt.Valid() && newt.Parent()==this
    ensures x in old(Model()) ==> newt.HasPeek?() && newt.Peek?() == x
    ensures x !in old(Model()) ==> newt.Traversed() == Model() && |newt.Traversed()| == |Model()|

    ensures x in old(Model()) ==> (newt as OrderedSetIteratorForward).Index() == |smaller(Model(),x)| //NEW
    ensures x !in old(Model()) ==> (newt as OrderedSetIteratorForward).Index() == |Model()|

    ensures Iterators() >= {newt}+old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
              && it.Valid()
              && it.Parent() == old(it.Parent())
              && it.Traversed() == old(it.Traversed())
              && |it.Traversed()| == old(|it.Traversed()|)
              && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

    ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
              (it is OrderedSetIteratorForward &&
               (it as OrderedSetIteratorForward).Index() == old((it as OrderedSetIteratorForward).Index()))

  method Insert(mid: UnorderedSetIterator, x: K) returns (newt:UnorderedSetIterator)
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
    //mid just a hint, it is inserted where corresponds
    //efficiently or not if it respects order
    requires mid.Parent() == this
    requires mid in Iterators()

    ensures newt is OrderedSetIteratorForward
    ensures fresh(newt)
    ensures newt.Valid() && newt.Parent()==this
    ensures newt.HasPeek?() && newt.Peek?()==x

    ensures (newt as OrderedSetIteratorForward).Index() ==  |smaller(Model(),x)|//NEW

    ensures Iterators() >= {newt}+old(Iterators())


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

    ensures next is OrderedSetIteratorForward
    ensures fresh(next)
    ensures next.Valid() && next.Parent()==this
    ensures next.Traversed()==old(mid.Traversed())
    ensures |next.Traversed()| == old(|mid.Traversed()|)

    ensures mid is OrderedSetIteratorForward && (next as OrderedSetIteratorForward).Index() == old((mid as OrderedSetIteratorForward).Index())

    ensures Iterators() >= {next}+old(Iterators())

}

method {:verify false} {:timeLimitMultiplier 100} try(s:OrderedSetForward)
  modifies s, s.Repr()
  requires s.Valid() && s.Empty?()
  requires allocated(s.Repr())
  ensures s.Valid()
  ensures fresh(s.Repr()-old(s.Repr()))
  ensures  allocated(s.Repr())
{


  s.Add(2); s.Add(7); s.Add(0); s.Add(1);s.Add(10);
  assert s.Model()=={0,1,2,7,10};

  var b:=s.Contains(10);
  assert b;

  var it : OrderedSetIteratorForward :=s.First(); var cont:=0;
  b := it.HasPeek();
  while (b)
    //decreases |s.Model()|-|it.Traversed()|
    decreases |s.Model()|-it.Index()
    invariant it.Valid() && it.Parent()==s
    invariant s.Valid() && s.Model()=={0,1,2,7,10}
    invariant  allocated(s.Repr())
    invariant fresh(s.Repr()-old(s.Repr()))
    invariant b == it.HasPeek?()
  { var aux := it.Peek();
    it.Next();
    if (aux%2==0) {cont:=cont+1;}
    b := it.HasPeek();
  }

  assert s.Model()=={0,1,2,7,10};
  var it2 :=s.Find(2) ;
  assert it2 is OrderedSetIteratorForward;
  assert s is OrderedSetForward;
  assert 2 in s.Model();
  assert it2.Peek?()==2;
  assert it2.Peek?()!=5;
  assert (it2 as OrderedSetIteratorForward).Traversed()=={0,1};//OO(
  assert it2.Index()==2;
  it2:=s.Find(7);
  assert it2.Traversed()=={0,1,2};
  assert it2.Index()==3;
  assert it2.Peek?()==7;
  it2.Next();
  assert it2.Index()==4;

  var it3:OrderedSetIteratorForward:=s.Find(7);
  it3:=s.Insert(it3,5);//efficient
  assert it3.Traversed()=={0,1,2};
  assert it3.Index()==3;
  it3:=s.Insert(it3,12);
  assert it3.Traversed()=={0,1,2,5,7,10};
  assert it3.Index()==6;
  //assert maximum(it3.Traversed())==10;

}
}
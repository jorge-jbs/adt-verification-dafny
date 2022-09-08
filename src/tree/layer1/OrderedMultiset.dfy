include "../../../src/tree/layer1/UnorderedMultiset.dfy"
include "../../../src/tree/layer1/OrderedMultisetUtils.dfy"


trait OrderedMultisetIterator extends UnorderedMultisetIterator{
  
  function Traversed():multiset<int>
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    ensures Traversed()<=Parent().Model()
    ensures forall x,y | x in Traversed() && y in Parent().Model()-Traversed() :: x<=y

   //Several elements equal to the Peek may be in Traversed and some others not
  // Example: Model=={1,1,2,3,3,3,4,5} Traversed=={1,1,2,3,3} Peek=3 

  function method Peek(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() in Parent().Model() && (Parent().Model()-Traversed())[Peek()]>0
    ensures Peek()==elemth(Parent().Model(),|Traversed()|)
    ensures forall x | x in Traversed() :: x<=Peek()
    ensures forall x | x in Parent().Model()-Traversed() :: Peek()<=x 


  function method Index(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext() ==> Index()==|Traversed()|
    ensures !HasNext() ==> Index()==|Parent().Model()|

  method Next() returns (x: int)
    modifies this
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    requires allocated(Parent())
    requires forall it | it in Parent().Repr() :: allocated(it)
    ensures Parent().Valid()
    ensures Valid()
    ensures old(Parent()) == Parent()
    ensures old(Parent().Model()) == Parent().Model()

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures x==old(Peek()) && Traversed() == multiset{old(Peek())}+old(Traversed()) 
    ensures |Traversed()|==1+|old(Traversed())|
    ensures HasNext() ==> Peek()==elemth(Parent().Model(),|Traversed()|)//already known


    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek())))

  function method HasPrev(): bool//igual que HasNext
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasPrev()  <==> Traversed() < Parent().Model() && |Traversed()| < |Parent().Model()|
    //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()|-|it.Traversed()|
    ensures !HasPrev() ==> Traversed() == Parent().Model() && |Traversed()| == |Parent().Model()|
  

  method Prev() returns (x: int)
    modifies this
    requires Valid()
    requires Parent().Valid()
    requires HasNext() 
    requires allocated(Parent())
    requires forall it | it in Parent().Repr() :: allocated(it)
    ensures Parent().Valid()
    ensures Valid()
    ensures old(Parent()) == Parent()
    ensures old(Parent().Model()) == Parent().Model()

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures x==old(Peek())  
    ensures old(Traversed())==multiset{} ==> Traversed()==Parent().Model()
    ensures old(Traversed())!=multiset{} ==> Traversed()==old(Traversed())-multiset{maximum(old(Traversed()))}
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek())))

  method Copy() returns (it: UnorderedMultisetIterator)
    modifies Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Iterators() :: allocated(it)
    ensures fresh(it)
    ensures Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Valid()
    ensures Parent().Model() == old(Parent().Model())

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)
    
    ensures it is OrderedMultisetIterator
    ensures it.Valid()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()

    ensures Traversed() == it.Traversed() 
    ensures HasNext() ==> Peek()==it.Peek()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))

  
}

trait OrderedMultiset extends UnorderedMultiset{
  
   //Novelties respect UnorderedSet
   // Last iterator method 
   // Find knows the traversed elements
   // Insert knows the traversed elements
   // Those methods that return iterators do return OrderedSetIterator
   // Methods receiving iterators may be called with OrderedSetIterator
   // The rest remains the same 

  function Iterators(): set<UnorderedMultisetIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
    ensures forall it | it in Iterators() :: it is OrderedMultisetIterator

  method First() returns (it: UnorderedMultisetIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures it is OrderedMultisetIterator
    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Traversed()==multiset{} 
    ensures Model()!=multiset{} ==> it.HasNext() && it.Peek()==elemth(Model(),0)
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))


  method Last() returns (it: OrderedMultisetIterator)//iterator to the last element
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures Model()!=multiset{} ==> it.HasNext() && it.Traversed()==Model()-multiset{elemth(Model(),|Model()|-1)} && it.Peek()==elemth(Model(),|Model()|-1)
    ensures Model()==multiset{} ==> it.Traversed()==multiset{}
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))


  method find(x:int) returns (newt:UnorderedMultisetIterator )
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures Model()==old(Model())

    ensures newt is OrderedMultisetIterator
    ensures fresh(newt) 
    ensures newt.Valid() && newt.Parent()==this
    ensures x in Model() ==> newt.HasNext() && newt.Traversed()==msmaller(Model(),x) && newt.Peek()==x //points to the first occurrence
    ensures x !in Model() ==> newt.Traversed()==Model()

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == {newt}+old(Iterators())

  method insert(mid: UnorderedMultisetIterator, x: int) returns (newt:UnorderedMultisetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid() 
    //mid just a hint, it is inserted where corresponds
    //efficiently or not if it respects order
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + multiset{x}

    
    ensures newt is OrderedMultisetIterator
    ensures fresh(newt)
    ensures Iterators() == {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this
    ensures newt.HasNext() && 
            msmaller(Model(),x)<=newt.Traversed()<=msmaller(Model(),x)[x:=old(Model())[x]] &&
            newt.Peek()==x 
            //Example: 1,2,2,2,2,3 insert another 2 , Traversed may be 
            //{1} (newt points to the first 2), {1,2}, ..., {1,2,2,2,2} (newt points to the last 2)
    
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    //points either to the inserted elemento or to the already existing one

  method erase(mid:UnorderedMultisetIterator) returns (next: UnorderedMultisetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model())-multiset{old(mid.Peek())}
    
    ensures next is OrderedMultisetIterator
    ensures fresh(next)
    ensures Iterators() == {next}+old(Iterators())
    ensures next.Valid() && next.Parent()==this 
    ensures next.Traversed()==old(mid.Traversed())  &&
           (next.HasNext() ==> next.Peek()==elemth(Model(),|next.Traversed()|))

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

}


/*
method {:verify true} try(s:OrderedSet)
modifies s, s.Repr()
requires s.Valid() && s.Empty()
requires forall x | x in s.Repr() :: allocated(x)
ensures s.Valid()
ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
ensures fresh(s.Repr()-old(s.Repr()))
ensures forall x | x in s.Repr() :: allocated(x)
{

 
 s.add(2); s.add(7); s.add(0); s.add(1);s.add(10);
 assert s.Model()=={0,1,2,7,10};

 var b:=s.contains(10);
 assert b;
*/
 /*var it : OrderedSetIterator :=s.First(); var cont:=0;
  while (it.HasNext())
  //decreases |s.Model()|-|it.Traversed()|
  decreases |s.Model()|-it.Index()
  invariant it.Valid() && it.Parent()==s
  invariant s.Valid() && s.Model()=={0,1,2,7,10}
  invariant  forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
  invariant fresh(s.Repr()-old(s.Repr()))
  invariant forall x | x in s.Repr() :: allocated(x)
    {var aux:=it.Next();
     if (aux%2==0) {cont:=cont+1;} 
    } 
*/
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
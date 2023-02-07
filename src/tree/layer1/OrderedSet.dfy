include "../../../src/tree/layer1/UnorderedSet.dfy"
include "../../../src/tree/layer1/OrderedSetUtils.dfy"


trait OrderedSetIterator extends UnorderedSetIterator<int>{
  
  //Here "traversed" means those smaller than the element
  //it does not mean if they have been traversed or not
  //They are the |Traversed()| smaller elements of the set
  //Peek is uniquely determined from the parent set and the size of traversed, so Traversed is enough
  //However I add all the knowledge to the postconditions about both 

  
  function Traversed():set<int>
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    ensures Traversed() <= Parent().Model()
    ensures forall x,y | x in Traversed() && y in Parent().Model()-Traversed() :: x < y

  function Peek?():int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    requires HasPeek?()
    
    ensures Peek?() in Parent().Model() && Peek?() !in Traversed()
    //ensures Peek?() == elemth(Parent().Model(),|Traversed()|)
    ensures forall x | x in Traversed() :: x < Peek?()
    //ensures forall x | x in Parent().Model()-Traversed()-{Peek?()} :: Peek?() < x
    //ensures forall x | x in Parent().Model()-Traversed() :: Peek?() <= x
  {  lelemth(Parent().Model(),|Traversed()|);
     elemth(Parent().Model(),|Traversed()|)
  }

  function Index(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasPeek?()  ==> Index()==|Traversed()|==|smaller(Parent().Model(),Peek?())|
    ensures !HasPeek?() ==> Index()==|Parent().Model()|
  {

    |Traversed()|
  }

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

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures Traversed() == {old(Peek?())}+old(Traversed()) 
    ensures |Traversed()| == 1+|old(Traversed())|
    ensures HasPeek?() ==> Peek?() == elemth(Parent().Model(),|Traversed()|)//already known

   ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && (it != this ==> it.Traversed() == old(it.Traversed())
                         && (it.HasPeek?() ==> it.Peek?()==old(it.Peek?())))
 

  method Prev() returns (x: int)
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

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures old(Traversed()) == {} ==> Traversed() == Parent().Model()
    ensures old(Traversed()) != {} ==> (Traversed()==old(Traversed())-{maximum(old(Traversed()))} &&
                                      (HasPeek?() ==> Peek?() == maximum(old(Traversed()))))
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && (it != this ==> it.Traversed() == old(it.Traversed())
                         && (it.HasPeek?() ==> it.Peek?()==old(it.Peek?())))
 
  
}

/*trait OrderedSet extends UnorderedSet{
  
   //Novelties respect UnorderedSet
   // Last iterator method 
   // Find knows the traversed elements
   // Insert knows the traversed elements
   // Those methods that return iterators do return OrderedSetIterator
   // Methods receiving iterators may be called with OrderedSetIterator
   // The rest remains the same 

  function Iterators(): set<UnorderedSetIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
    ensures forall it | it in Iterators() :: it is OrderedSetIterator

  method First() returns (it: UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures it is OrderedSetIterator
    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Traversed()=={} 
    ensures Model()!={} ==> it.HasNext() && it.Peek()==elemth(Model(),0)
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))


  method Last() returns (it: OrderedSetIterator)//iterator to the last element
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
    ensures Model()!={} ==> it.HasNext() && it.Traversed()==Model()-{elemth(Model(),|Model()|-1)} && it.Peek()==elemth(Model(),|Model()|-1)
    ensures Model()=={} ==> it.Traversed()=={}
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek()==old(it.Peek()))


  method find(x:int) returns (newt:UnorderedSetIterator )
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures Model()==old(Model())
    ensures newt is OrderedSetIterator
    ensures fresh(newt) 
    ensures newt.Valid() && newt.Parent()==this
    ensures x in Model() ==> newt.HasNext() && newt.Traversed()==smaller(Model(),x) && newt.Peek()==x
    ensures x !in Model() ==> newt.Traversed()==Model()

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == {newt}+old(Iterators())

  method insert(mid: UnorderedSetIterator, x: int) returns (newt:UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid() 
    //mid just a hint, it is inserted where corresponds
    //efficiently or not if it respects order
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + {x}

    
    ensures newt is OrderedSetIterator
    ensures fresh(newt)
    ensures Iterators() == {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this
    ensures newt.HasNext() && newt.Traversed()==smaller(Model(),x) && newt.Peek()==x
    
    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    //points either to the inserted elemento or to the already existing one

  method erase(mid:UnorderedSetIterator) returns (next: UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model())-{old(mid.Peek())}
    
    ensures next is OrderedSetIterator
    ensures fresh(next)
    ensures Iterators() == {next}+old(Iterators())
    ensures next.Valid() && next.Parent()==this 
    ensures next.Traversed()==old(mid.Traversed())  && 
            (next.HasNext() ==> next.Peek()==elemth(Model(),|next.Traversed()|))

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

}



method {:verify false} try(s:OrderedSet)
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
   assert s.Model()=={0,1,2,7,10};
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

  assert s.Model()=={0,1,2,5,7,10,12};
  var it4:=s.Last();
  assert it4.Peek()==12;
    assert it4.Traversed()=={0,1,2,5,7,10};
  assert forall x | x in it4.Traversed() && x!=10 :: x < 10;
  lmaximumrev(it4.Traversed(),10);
    assert maximum(it4.Traversed())==10;

  var it5:OrderedSetIterator:=s.First();
  z:=it5.Prev();
  assert !it5.HasPrev();


}*/
include "../../../src/tree/layer1/UnorderedMap.dfy"
include "../../../src/tree/layer1/OrderedSetUtils.dfy"

trait OrderedMapIterator extends UnorderedMapIterator{

  function Traversed(): set<K>
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid() 
    ensures Traversed() <= (Parent().Model().Keys)
    ensures forall x,y | x in Traversed() && y in Parent().Model().Keys - Traversed() :: x < y

  function method Peek(): pairKV 
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() in Parent().Model().Items &&
            key(Peek()) !in Traversed() 
    ensures key(Peek()) == elemth(Parent().Model().Keys,|Traversed()|)  &&
            value(Peek()) == Parent().Model()[key(Peek())]      
    ensures forall k | k in Traversed() :: k < key(Peek())
    ensures forall k | k in Parent().Model().Keys - Traversed() - {key(Peek())} :: key(Peek()) < k
    ensures forall k | k in Parent().Model().Keys - Traversed() :: key(Peek()) <= k

  

  function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext()  <==> Traversed() < Parent().Model().Keys && |Traversed()| < |Parent().Model().Keys|
    //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()| - |it.Traversed()|
    ensures !HasNext() ==> Traversed() == Parent().Model().Keys && |Traversed()| == |Parent().Model().Keys|
  
  function method Index(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext() ==> Index() == |Traversed()| == |smaller(Parent().Model().Keys,key(Peek()))|
    ensures !HasNext() ==> Index() == |Parent().Model()|
  

  method Next() returns (p: pairKV)
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
    ensures fresh(Parent().Repr() - old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())

    ensures p == old(Peek()) && Traversed() == {old(key(Peek()))} + old(Traversed())
    ensures |Traversed()| == 1 + |old(Traversed())|
    ensures HasNext() ==> key(Peek()) == elemth(Parent().Model().Keys,|Traversed()|)//already known

    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek() == old(it.Peek())))

  function method HasPrev(): bool//igual que HasNext
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasPrev()  <==> Traversed() < Parent().Model().Keys && |Traversed()| < |Parent().Model().Keys|
    //|Traversed()| < |Parent().Model()| es necesario para poder verificar con cota |s.Model()| - |it.Traversed()|
    ensures !HasPrev() ==> Traversed() == Parent().Model().Keys && |Traversed()| == |Parent().Model().Keys|
  

  method Prev() returns (p: pairKV)
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
    ensures fresh(Parent().Repr() - old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures p == old(Peek())  
    ensures old(Traversed()) == {} ==> Traversed() == Parent().Model().Keys
    ensures old(Traversed()) != {} ==> (Traversed() == old(Traversed()) - {maximum(old(Traversed()))} &&
                                      (HasNext() ==> key(Peek()) == maximum(old(Traversed()))))
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek() == old(it.Peek())))

  method Copy() returns (it: UnorderedMapIterator)
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
    ensures fresh(Parent().Repr() - old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)
    
    ensures it is OrderedMapIterator
    ensures it.Valid()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()

    ensures Traversed() == it.Traversed() 
    ensures HasNext() ==> Peek() == it.Peek()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek() == old(it.Peek()))


}

trait OrderedMap extends UnorderedMap {
  
 
  function Iterators(): set<UnorderedMapIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
    ensures forall it | it in Iterators() :: it is OrderedMapIterator

  method First() returns (it: UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures it is OrderedMapIterator
    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Traversed() == {} 
    ensures Model() != map[] ==> it.HasNext() && key(it.Peek()) == elemth(Model().Keys,0)
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek() == old(it.Peek()))

  method Last() returns (it: OrderedMapIterator)//iterator to the last element
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Parent() == this
    ensures Model() != map[] ==> it.HasNext() && it.Traversed() == Model().Keys - {elemth(Model().Keys,|Model().Keys| - 1)} && key(it.Peek()) == elemth(Model().Keys,|Model().Keys| - 1)
    ensures Model() == map[] ==> it.Traversed() == {}
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Traversed() == old(it.Traversed()) && (it.HasNext() ==> it.Peek() == old(it.Peek()))




  method find(k: K) returns (newt: UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures Model() == old(Model())
    
    ensures newt is OrderedMapIterator
    ensures fresh(newt) 
    ensures newt.Valid() && newt.Parent() == this
    ensures k in old(Model()) ==> newt.HasNext() && key(newt.Peek()) == k
    ensures k !in old(Model()) ==> newt.Traversed() == Model().Keys

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == {newt} + old(Iterators())

  method insert(mid: UnorderedMapIterator, k: K, v : V) returns (newt: UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid() 
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())[k := v]

    ensures newt is OrderedMapIterator
    ensures fresh(newt)
    ensures Iterators() == {newt} + old(Iterators())
    ensures newt.Valid() && newt.Parent() == this  
    ensures newt.HasNext() && newt.Peek() == (k,v) && newt.Traversed() == smaller(Model().Keys,k)

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    //points either to the inserted elemento or to the already existing one
 



  method erase(mid: UnorderedMapIterator) returns (next: UnorderedMapIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== map k | k in old(Model()) && k != old(key(mid.Peek())) :: old(Model())[k]
    
    ensures next is OrderedMapIterator
    ensures fresh(next)
    ensures Iterators() == {next} + old(Iterators())
    ensures next.Valid() && next.Parent() == this 
    ensures next.Traversed() == old(mid.Traversed()) &&
                (next.HasNext() ==> key(next.Peek()) == elemth(Model().Keys,|next.Traversed()|) && value(next.Peek()) == Model()[key(next.Peek())])


    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
 
}
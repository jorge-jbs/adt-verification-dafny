include "../../../src/tree/layer1/UnorderedSet.dfy"






trait UnorderedSetLinkedList extends UnorderedSet {


  method contains(x:int) returns (b:bool)
   modifies this, Repr()
   requires Valid()
   requires forall x | x in Repr() :: allocated(x)
   ensures Valid() && Model()==old(Model())
   ensures b==(x in Model())
   
   ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
   ensures fresh(Repr()-old(Repr()))
   ensures forall x | x in Repr() :: allocated(x)
   
   ensures Iterators() == old(Iterators())
   ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && 
      it.Traversed() == old(it.Traversed()) && 
      (it.HasNext() ==> it.Peek()==old(it.Peek()))

 
  

  method add(x:int)
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + {x} 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
   
    ensures Iterators() == old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() &&
      (if !old(it.HasNext()) then
          it.Traversed() == Model()
      else
          it.Traversed() == old(it.Traversed()) &&
          it.HasNext() && 
          it.Peek()==old(it.Peek()))
      




  method remove(x:int) 
    modifies this,Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model()== old(Model()) - {x} 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) 
             && (!old(it.HasNext()) || (old(it.HasNext()) && old(it.Peek())!=x) )::
      it.Valid() && 
      it.Traversed() == old(it.Traversed())-{x} &&
      (it.HasNext() && old(it.Peek())!=x ==> it.Peek()==old(it.Peek()))
    

  method find(x:int) returns (newt:UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid() 
    ensures Model()==old(Model())
    
    ensures fresh(newt) 
    ensures newt.Valid() && newt.Parent()==this
    ensures x in old(Model()) ==> newt.HasNext() && newt.Peek()==x
    ensures x !in old(Model()) ==> newt.Traversed()==Model()

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == {newt}+old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && 
      it.Traversed() == old(it.Traversed()) &&
      (it.HasNext() ==> it.Peek()==old(it.Peek()))

  

  method insert(mid: UnorderedSetIterator, x: int) returns (newt:UnorderedSetIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid() 
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + {x}

    ensures fresh(newt)
    ensures Iterators() == {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this  
    ensures newt.HasNext() && newt.Peek()==x 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() &&
      (if !old(it.HasNext()) then
          it.Traversed() == Model()
      else
          it.Traversed() == old(it.Traversed()) &&
          it.HasNext() && it.Peek()==old(it.Peek()))
      



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
    
    ensures fresh(next)
    ensures Iterators() == {next}+old(Iterators())
    ensures next.Valid() && next.Parent()==this 
    ensures next.Traversed()==old(mid.Traversed()) 

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures forall it | it in old(Iterators()) && old(it.Valid()) 
             && (!old(it.HasNext()) || (old(it.HasNext()) && old(it.Peek())!=old(mid.Peek())) )::
      it.Valid() && 
      it.Traversed() == old(it.Traversed())-{old(mid.Peek())} &&
      (it.HasNext() && old(it.Peek())!=old(mid.Peek()) ==> it.Peek()==old(it.Peek()))
 

}



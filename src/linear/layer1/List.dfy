include "../../../src/Utils.dfy"
include "../../../src/linear/layer1/ADT.dfy"

trait ListIterator<A> {
  function Parent(): List<A>
    reads this

  predicate Valid()
    reads this, Parent(), Parent().Repr()
    ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()

  function Index(): nat
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures Index() <= |Parent().Model()|

  predicate HasNext?() 
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
  {  Index() < |Parent().Model()| }

  method HasNext() returns (b:bool) 
    modifies this, Parent(), Parent().Repr()
    requires allocated(Parent())
    requires allocated(Parent().Repr())
    
    requires Valid()
    requires Parent().Valid()
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Model() == old(Parent().Model()) 
    ensures Index()==old(Index())
    ensures b == HasNext?()

    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures allocated(Parent().Repr())

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())

  method Next() returns (x: A)
    modifies this, Parent(), Parent().Repr()
    requires allocated(Parent())
    requires allocated(Parent().Repr())
    
    requires Valid()
    requires Parent().Valid()
    requires HasNext?()
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())  
    ensures Parent().Model() == old(Parent().Model())  

    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures allocated(Parent().Repr())

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures x == Parent().Model()[old(Index())]
    ensures Index() == 1 + old(Index())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent()==old(it.Parent()) && (it != this ==> it.Index() == old(it.Index()))

  
  method Peek() returns (p:A)
    modifies this, Parent(), Parent().Repr()
    requires allocated(Parent())
    requires allocated(Parent().Repr())
    
    requires Valid()
    requires Parent().Valid()
    requires HasNext?()
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())  
    ensures Parent().Model() == old(Parent().Model())  
    ensures Index() == old(Index())
    ensures p==Parent().Model()[Index()] 
    
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures allocated(Parent().Repr())

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent()==old(it.Parent()) && it.Index() == old(it.Index())


  method Copy() returns (it: ListIterator<A>)
    modifies this, Parent(), Parent().Repr()
    requires allocated(Parent())
    requires allocated(Parent().Repr())
    
    requires Valid()
    requires Parent().Valid()
    ensures fresh(it)
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Model() == old(Parent().Model())
    ensures Index()==old(Index())

    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures allocated(Parent().Repr())
    
    ensures it.Valid()
    ensures Parent().Iterators() >= {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()
    ensures Index() == it.Index()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent()==old(it.Parent()) && it.Index() == old(it.Index())

  method Set(x: A) 
    modifies this, Parent(), Parent().Repr()
    requires allocated(Parent())
    requires allocated(Parent().Repr())
   
    requires Valid()
    requires Parent().Valid()
    requires HasNext?()
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())
    ensures |Parent().Model()| == old(|Parent().Model()|)
    ensures Index() == old(Index()) 
    ensures Parent().Model()==old(Parent().Model()[Index():=x])
    
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures allocated(Parent().Repr())

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent()==old(it.Parent()) && it.Index() == old(it.Index())
}

trait List<A> extends ADT<seq<A>> {
  predicate Empty?()
    reads this, Repr()
    requires Valid()
  { Model() == []}

  method Empty() returns (b:bool)
    modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures b==Empty?() 

    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())
 
    ensures Iterators() >= old(Iterators())

  method Size() returns (s:nat)
    modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures s==|Model()| 

    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    ensures Iterators() >= old(Iterators())

  function Iterators(): set<ListIterator<A>>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this

  method Begin() returns (it: ListIterator<A>)
    modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())

    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    ensures fresh(it)
    ensures Iterators() >= {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Index() == 0
    ensures it.Parent() == this
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent()==old(it.Parent()) && it.Index() == old(it.Index())

  method Front() returns (x:A)
    modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[0]

    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())
 
    ensures Iterators() >= old(Iterators())
  
  method PushFront(x: A)
    modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    ensures Iterators() >= old(Iterators())

  method PopFront() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
   
    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures [x] + Model() == old(Model())

    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    ensures Iterators() >= old(Iterators())

  method Back() returns (x:A)//Nuevo metodo
    modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[|Model()|-1]

    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())
 
    ensures Iterators() >= old(Iterators())
  
  method PushBack(x: A)
    modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]

    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    ensures Iterators() >= old(Iterators())

  method PopBack() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() + [x] == old(Model())

    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    ensures Iterators() >= old(Iterators())

  // Insertion of x before mid, newt points to x
  method Insert(mid: ListIterator<A>, x: A) returns (newt: ListIterator<A>)
    modifies this, Repr()
    requires allocated(Repr())

    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid in Iterators()
    ensures Valid()
    ensures Model() == Seq.Insert(x, old(Model()), old(mid.Index()))

    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    ensures fresh(newt)
    ensures Iterators() >= {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this && newt.Index()==old(mid.Index())
 

  // Deletion of mid, next points to the next element (or past-the-end)
  method Erase(mid: ListIterator<A>) returns (next: ListIterator<A>)
    modifies this, Repr()
    requires allocated(Repr())

    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext?()
    requires mid in Iterators()
    ensures Valid()
    ensures Model() == Seq.Remove(old(Model()), old(mid.Index()))

    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    ensures fresh(next)
    ensures Iterators() >= {next}+old(Iterators())
    ensures next.Valid() && next.Parent()==this && next.Index()==old(mid.Index())
}

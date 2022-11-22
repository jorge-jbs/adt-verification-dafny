include "../../../src/Utils.dfy"
include "../../../src/linear/layer1/ADT.dfy"

trait ListIterator<A> {
  function Parent(): List<A>
    reads this

  predicate Valid()
    reads this, Parent(), Parent().Repr()

  function Index(): nat
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures Index() <= |Parent().Model()|

  function HasNextF(): bool //Antiguo FM HasNext
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNextF() <==> Index() < |Parent().Model()|

  method HasNext() returns (b:bool) //Nuevo metodo
    modifies this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Repr() :: allocated(it) //duda con el nombre it
    ensures Valid()
    ensures Parent().Valid()
    ensures old(Parent()) == Parent()
    ensures old(Parent().Model()) == Parent().Model()
    ensures Index()==old(Index())//DUDA: redundante en este caso
    ensures b == HasNextF()//(Index() < |Parent().Model()|) ¿que queda mejor?

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())


  method Next() returns (x: A) //Añado Parent() y Parent().Repr()
    modifies this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Repr() :: allocated(it)
    requires HasNextF()
    ensures Valid()
    ensures Parent().Valid()
    ensures old(Parent()) == Parent()
    ensures old(Parent().Model()) == Parent().Model()

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures x == Parent().Model()[old(Index())]
    ensures Index() == 1 + old(Index())
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Index() == old(it.Index()))

  function  PeekF(): A //Antiguo FM Peek()
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNextF()
    ensures PeekF() == Parent().Model()[Index()]

  method Peek() returns (p:A)//nuevo metodo
    modifies this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Repr() :: allocated(it)
    requires HasNextF()
    ensures Valid()
    ensures Parent().Valid()
    ensures old(Parent()) == Parent()
    ensures old(Parent().Model()) == Parent().Model()
    ensures old(Index())==Index() //A pesar de la ultima postcondicion hace falta, así que no es tan redundante
    ensures p==PeekF()//Parent().Model()[Index()] ¿que queda mejor?

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())
    //ensures this in Parent().Iterators() && p==FPeek()//Parent().Model()[Index()] ¿que queda mejor?
    //Interesante, con esto si funciona, el iterador no sabe que esta en los iteradores de su padre


  method Copy() returns (it: ListIterator<A>)//Añado this a la clausula modifies
    modifies this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Iterators() :: allocated(it)
    ensures fresh(it)
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Model() == old(Parent().Model())
    ensures Index()==old(Index())//Añadido

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)
    
    ensures it.Valid()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()
    ensures Index() == it.Index()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())

  method Set(x: A) //Añado Parent() y Parent().Repr()
    modifies this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Repr() :: allocated(it)
    requires HasNextF()
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())
    ensures |Parent().Model()| == old(|Parent().Model()|)
    ensures Parent().Model()[old(Index())] == x
    ensures forall i | 0 <= i < |Parent().Model()| && i != old(Index()) ::
      Parent().Model()[i] == old(Parent().Model()[i])
    ensures Index() == old(Index()) //Añadido


    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())
}

trait List<A> extends ADT<seq<A>> {
  function EmptyF(): bool //Antiguo FM Empty
    reads this, Repr()
    requires Valid()
    ensures EmptyF() <==> Model() == []

  method Empty() returns (b:bool)//Nuevo metodo
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())
    ensures b==EmptyF() // Model() == [] ¿cual es mas bonita?

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
 
    ensures Iterators() == old(Iterators())


  function SizeF(): nat //Antiguo FM Size
    reads this, Repr()
    requires Valid()
    ensures SizeF() == |Model()|

  method Size() returns (s:int)//Nuevo metodo
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())
    ensures s==SizeF() //  |Model()| ¿cual es mas bonita?

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
 
    ensures Iterators() == old(Iterators())

  function Iterators(): set<ListIterator<A>>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this

  method Begin() returns (it: ListIterator<A>)
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
    ensures it.Index() == 0
    ensures it.Parent() == this
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())

  function FrontF(): A //Antiguo FM Front
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures FrontF() == Model()[0]

  method Front() returns (s:A)//Nuevo metodo
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    requires !EmptyF()
    ensures Valid()
    ensures Model() == old(Model())
    ensures s==FrontF() //  Model()[0] ¿cual es mas bonita?

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
 
    ensures Iterators() == old(Iterators())
  

  method PushFront(x: A)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())

  method PopFront() returns (x: A)
    modifies this, Repr()
    requires Valid()
    requires Model() != []
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures [x] + Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())

  function BackF(): A //Antiguo FM Back
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures BackF() == Model()[|Model()|-1]

  method Back() returns (s:A)//Nuevo metodo
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    requires !EmptyF()
    ensures Valid()
    ensures Model() == old(Model())
    ensures s==BackF() //  Model()[|Model()|-1] ¿cual es mas bonita?

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
 
    ensures Iterators() == old(Iterators())
  

  method PushBack(x: A)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + [x]

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())

  method PopBack() returns (x: A)
    modifies this, Repr()
    requires Valid()
    requires Model() != []
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() + [x] == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())

  // Insertion of x before mid, newt points to x
  method Insert(mid: ListIterator<A>, x: A) returns (newt: ListIterator<A>)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == Seq.Insert(x, old(Model()), old(mid.Index()))

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(newt)
    ensures Iterators() == {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this && newt.Index()==old(mid.Index())
 

  // Deletion of mid, next points to the next element (or past-the-end)
  method Erase(mid: ListIterator<A>) returns (next: ListIterator<A>)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNextF()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == Seq.Remove(old(Model()), old(mid.Index()))

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(next)
    ensures Iterators() == {next}+old(Iterators())
    ensures next.Valid() && next.Parent()==this && next.Index()==old(mid.Index())
}

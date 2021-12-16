include "../../Utils.dfy"
include "../adt/List.dfy"


trait ArrayListIterator extends ListIterator {
  predicate Valid()
    reads this, Parent(), Parent().Repr()

  function Parent(): List
    reads this
    ensures Parent() is ArrayList

  function Index() : nat
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures Index() <= |Parent().Model()|

  function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext() <==> Index() < |Parent().Model()|

  function method Peek(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() == Parent().Model()[Index()]

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
    ensures old(Parent().Model()) == Parent().Model()       // ?

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr() - old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())   // ?
    ensures x == Parent().Model()[old(Index())]
    ensures Index() == 1 + old(Index())
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
       it.Valid() && (it != this ==> it.Index() == old(it.Index()))

  method Copy() returns (it: ListIterator)
    modifies Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Iterators() :: allocated(it)
    ensures fresh(it)
    ensures Valid()
    ensures it.Valid()
    ensures Parent().Valid()

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures it in Parent().Iterators()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == old(Parent())
    ensures Parent() == it.Parent()
    ensures Index() == it.Index()
    ensures it.Valid()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
    it.Valid() && it.Index() == old(it.Index())
    ensures Parent().Model() == old(Parent().Model())
}


trait ArrayList extends List {

  function method Front(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []
    
    ensures Valid()
    ensures Front() == Model()[0]

  method PushFront(x: int)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in old(Iterators()) :: old(it.Valid())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();


  method PopFront() returns (x: int)
    modifies this, Repr()
    requires Valid()
    requires Model() != []
    requires forall x | x in Repr() :: allocated(x)

    ensures Valid()
    ensures [x] + Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in old(Iterators()) :: old(it.Valid()) && old(it.HasNext())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();

  function method Back(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []
    
    ensures Valid()
    ensures Back() == Model()[|Model()|-1]

  method PopBack() returns (x: int)
    modifies this, Repr()
    requires Valid()
    requires Model() != []
    requires forall x | x in Repr() :: allocated(x)
    
    ensures Valid()
    ensures Model() + [x] == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in old(Iterators()) :: old(it.Valid()) && old(it.HasNext())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();

  method PushBack(x: int)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    
    ensures Valid()
    ensures Model() == old(Model()) + [x]

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in old(Iterators()) :: old(it.Valid())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();

  method Begin() returns (it: ListIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr()::allocated(x)
    
    ensures Valid()
    ensures Model() == old(Model())

    ensures it is ArrayListIterator
    ensures fresh(it)
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Index() == 0

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == {it} + old(Iterators())
    ensures forall it | it in old(Iterators()) :: old(it.Valid())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();

  method Insert(mid: ListIterator, x: int)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)

    ensures Valid()
    ensures Model() == Seq.Insert(x, old(Model()), old(mid.Index()))

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in old(Iterators()) :: old(it.Valid())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();

  method Erase(mid: ListIterator) returns (next: ListIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    
    ensures Valid()
    ensures Model() == Seq.Remove(old(Model()), old(mid.Index()))

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(next)
    ensures Iterators() == {next} + old(Iterators())
    ensures forall it | it in old(Iterators()) :: old(it.Valid()) && old(it.HasNext())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();    
    ensures next.Valid() && next.Parent() == this && next.Index() == mid.Index();
}


method Test(l: ArrayList)
  requires l.Valid() && l.Model() == []
  requires forall x | x in l.Repr() :: allocated(x)
  modifies l, l.Repr()
{
  l.PushBack(10);
  l.PushBack(20);
  l.PushBack(30);
  var model := [10, 20, 30];
  assert l.Model() == model;

  var it := l.Begin();
  assert it.Peek() == 10;
  var _ := l.PopFront();
  assert l.Model() == model[1..];
  assert it.Peek() == 20;
  var _ := l.PopFront();
  assert l.Model() == model[2..];
  assert it.Peek() == 30;
  var _ := it.Next();
  assert !it.HasNext();
  var _ := l.PopFront();
  // assert it.Valid();    // assertion violation
}


method Test2(l1: ArrayList, l2: ArrayList)
  requires l1.Valid() && l2.Valid()
  requires forall x | x in l1.Repr() :: allocated(x)
  requires forall x | x in l2.Repr() :: allocated(x)
  requires {l1} + l1.Repr() !! {l2} + l2.Repr()
  requires l1.Model() == [1, 2, 3] && l2.Model() == [4, 5, 6]
  modifies l1, l2, l1.Repr(), l2.Repr()
{
  var model2 := l2.Model();
  var it1 := l1.Begin();
  var it2 := l2.Begin();
  assert it1.Peek() == 1 && it2.Peek() == 4;
  var _ := it1.Next();
  assert it1.Peek() == 2 && it2.Peek() == 4;
  var _ := l2.PopFront();
  assert l2.Model() == model2[1..];
  assert it1.Peek() == 2 && it2.Peek() == 5;
}
include "../../../src/Utils.dfy"
include "../../../src/linear/layer1/List.dfy"

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
    ensures forall it | it in old(Iterators()) && old(it.Valid())
      :: it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();


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
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasNext())
      :: it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();

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
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasNext())
      :: it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();

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
    ensures forall it | it in old(Iterators()) && old(it.Valid())
      :: it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();

  method Begin() returns (it: ListIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr()::allocated(x)
    
    ensures Valid()
    ensures Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(it)
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Index() == 0
    ensures Iterators() == {it} + old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid())
      :: it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();

  // Insertion of x before mid, newt points to x
  method Insert(mid: ListIterator, x: int) returns (newt:ListIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)

    ensures Valid()
    ensures Model() == Seq.Insert(x, old(Model()), old(mid.Index()))

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(newt)
    ensures Iterators() == {newt}+old(Iterators())
    ensures newt.Valid() && newt.Parent()==this && newt.Index()==old(mid.Index())
 
    ensures forall it | it in old(Iterators()) && old(it.Valid())
      :: it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();

  // Deletion of mid, next points to the next element (or past-the-end)
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
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasNext())
      :: it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index()
    ensures next.Valid() && next.Parent() == this && next.Index() == mid.Index()

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

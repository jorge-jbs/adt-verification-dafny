include "../../../src/Utils.dfy"
include "../../../src/linear/layer1/List.dfy"

trait ArrayList<A> extends List<A> {
  method PushFront(x: A)
    modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())

  method PopFront() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
   
    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures [x] + Model() == old(Model())

    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasNext?())
      :: it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())

  method PushBack(x: A)
    modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]

    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid())
      :: it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())

  method PopBack() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() + [x] == old(Model())

    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasNext?())
      :: it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
 
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

    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    ensures fresh(newt)
    ensures Iterators() >= {newt} + old(Iterators())
    ensures newt.Valid() && newt.Parent() == this && newt.Index() == old(mid.Index())
 
    ensures forall it | it in old(Iterators()) && old(it.Valid())
      :: it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())


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

    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    ensures fresh(next)
    ensures Iterators() >= {next} + old(Iterators())
    ensures next.Valid() && next.Parent() == this && next.Index() == old(mid.Index())
     ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasNext?())
      :: it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
}


method Test(l: ArrayList<int>)
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
  assert it.Parent().Model()[it.Index()] == 10;
  var _ := l.PopFront();
  assert l.Model() == model[1..];
  assert  it.Parent().Model()[it.Index()] == 20;
  var _ := l.PopFront();
  assert l.Model() == model[2..];
  assert  it.Parent().Model()[it.Index()] == 30;
  var _ := it.Next();
  assert !it.HasNext?();
  var _ := l.PopFront();
  // assert it.Valid();    // assertion violation
}


method Test2(l1: ArrayList<int>, l2: ArrayList<int>)
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
  assert it1.Parent().Model()[it1.Index()] == 1 && it2.Parent().Model()[it2.Index()] == 4;
  var _ := it1.Next();
  assert it1.Parent().Model()[it1.Index()] == 2 && it2.Parent().Model()[it2.Index()] == 4;
  var _ := l2.PopFront();
  assert l2.Model() == model2[1..];
  assert it1.Parent().Model()[it1.Index()]== 2 && it2.Parent().Model()[it2.Index()] == 5;
}

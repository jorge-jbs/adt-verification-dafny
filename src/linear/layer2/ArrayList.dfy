include "../../../src/Utils.dfy"
include "../../../src/linear/layer1/List.dfy"

trait ArrayList<A> extends List<A> {
  method PushFront(x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())

  method PopFront() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures [x] + Model() == old(Model())

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasPeek?())
      :: it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())

  method PushBack(x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid())
      :: it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())

  method PopBack() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() + [x] == old(Model())

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasPeek?())
      :: it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
 
  // Insertion of x before mid, newt points to x
  method Insert(mid: ListIterator<A>, x: A) returns (newt: ListIterator<A>)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid in Iterators()
    requires mid.HasPeek?()
    ensures Valid()
    ensures Model() == Seq.Insert(x, old(Model()), old(mid.Index()))

    ensures fresh(newt)
    ensures Iterators() >= {newt} + old(Iterators())
    ensures newt.Valid() && newt.Parent() == this && newt.Index() == old(mid.Index())
 
    ensures forall it | it in old(Iterators()) && old(it.Valid())
      :: it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())

  // Deletion of mid, next points to the next element (or past-the-end)
  method Erase(mid: ListIterator<A>) returns (next: ListIterator<A>)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasPeek?()
    requires mid in Iterators()
    ensures Valid()
    ensures Model() == Seq.Remove(old(Model()), old(mid.Index()))

    ensures fresh(next)
    ensures Iterators() >= {next}+old(Iterators())
    ensures next.Valid() && next.Parent() == this && next.Index() == old(mid.Index())
     ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasPeek?())
      :: it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
}


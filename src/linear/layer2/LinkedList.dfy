include "../../../src/Utils.dfy"
include "../layer1/List.dfy"

trait LinkedList<A> extends List<A> {
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
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index()) + 1

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
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.Index()) != 0 ::
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() + 1 == old(it.Index())

  method PushBack(x: A)
      modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]

    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      && it.Valid()
      && it.Parent() == old(it.Parent())
      && if old(it.Index()) == old(|Model()|) then
          it.Index() == 1 + old(it.Index())
        else
          it.Index() == old(it.Index())

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
    ensures
      forall it | it in old(Iterators()) && old(it.Valid()) && old(it.Index()) != old(|Model()| - 1) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && if old(it.Index()) == old(|Model()|) then
            it.Index() + 1 == old(it.Index())
           else
            it.Index() == old(it.Index())

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
 
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      && it.Valid()
      && it.Parent() == old(it.Parent())
      && if old(it.Index()) < old(mid.Index())  then
          it.Index() == old(it.Index())
         else
          it.Index() == old(it.Index()) + 1

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
    ensures forall it |
       && it in old(Iterators())
       && old(it.Valid())
       && old(it.Index()) != old(mid.Index()) ::
         && it.Valid() 
         && it.Parent() == old(it.Parent())
         && if old(it.Index()) < old(mid.Index())  then
             it.Index() == old(it.Index())
            else
             it.Index() == old(it.Index()) - 1
}

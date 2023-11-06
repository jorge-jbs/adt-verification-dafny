include "LinkedListSpec.dfy"
include "../List/ListSpec.dfy"
include "../DataStructures/DoublyLinkedListWithLast.dfy"

module LinkedListImpl{
  import opened ListSpec
  import opened LinkedListSpec
  import opened DoublyLinkedListWithLast

  export provides ListSpec, LinkedListSpec
         reveals LinkedListImpl

         provides LinkedListImpl.Model, LinkedListImpl.Valid, LinkedListImpl.ReprFamily
         provides LinkedListImpl.Empty, LinkedListImpl.Size
         provides LinkedListImpl.Front, LinkedListImpl.PushFront, LinkedListImpl.PopFront
         provides LinkedListImpl.Back, LinkedListImpl.PushBack, LinkedListImpl.PopBack
         provides LinkedListImpl.Iterators, LinkedListImpl.First, LinkedListImpl.Last
         provides LinkedListImpl.Insert, LinkedListImpl.Erase


class LinkedListIteratorImpl<A> extends ListIterator<A> {
  ghost var parent: LinkedListImpl<A>
  var node: DoublyLinkedList.DNode?<A>
  ghost var pastTheEnd: bool

  ghost predicate Valid()
    reads this, Parent(), Parent().Repr()
    ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()
  {
    && parent.Valid()
    && assert parent.Repr0() <= parent.ReprFamily(2); true
    && this in Parent().Iterators() //nuevo
    && (node != null ==> node in parent.list.list.spine)
  }

  ghost function Parent(): List<A>
    reads this
  {
    parent
  }

  ghost function Index(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures -1 <= Index() <= |Parent().Model()|

  {
    if node != null then
      parent.list.list.GetIndex(node)
    else if pastTheEnd then
      |parent.list.list.spine|
    else
      -1
  }

  constructor Internal(l: LinkedListImpl<A>, n: DoublyLinkedList.DNode<A>)
    modifies l`iters
    requires l.Valid() && n in l.Repr()
    requires n in l.list.list.spine
    ensures Valid()
    ensures Parent() == l
    ensures node == n
    ensures l.list == old(l.list) 
    ensures Index() == l.list.list.GetIndex(n)

    ensures l.Valid()
    ensures l.Iterators() == old(l.Iterators()) + { this }
    ensures l.Model() == old(l.Model())
    ensures fresh(l.Repr() - old(l.Repr()))

    ensures forall it | it in old(l.Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent())
      && it.Index() == old(it.Index())
  { 
    parent := l;
    node := n;
    pastTheEnd := false;
    new;
    parent.iters := l.iters + { this };
  }

  constructor First(l: LinkedListImpl<A>)
    modifies l`iters
    requires l.Valid()
    ensures Valid()
    ensures Parent() == l
    ensures Index() == 0
    ensures node == l.list.list.head
    ensures l.list == old(l.list) 

    ensures l.Valid()
    ensures l.Iterators() == old(l.Iterators()) + { this }
    ensures l.Model() == old(l.Model())
    ensures fresh(l.Repr() - old(l.Repr()))
    
    ensures forall it | it in old(l.Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent())
      && it.Index() == old(it.Index())
  {
    parent := l;
    node := l.list.list.head;
    pastTheEnd := true;
    new;
    parent.iters := l.iters + { this };
   }

  constructor Last(l: LinkedListImpl<A>)
    modifies l`iters
    requires l.Valid()
    ensures Valid()
    ensures Parent() == l
    ensures Index() == |l.Model()| - 1
    ensures node == l.list.last
    ensures l.list == old(l.list) 

    ensures l.Valid()
    ensures l.Iterators() == old(l.Iterators()) + { this }
    ensures l.Model() == old(l.Model())
    ensures fresh(l.Repr() - old(l.Repr()))

    ensures forall it | it in old(l.Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent())
      && it.Index() == old(it.Index())
 
  {
    parent := l;
    node := l.list.last;
    pastTheEnd := false;
    new;
    parent.iters := l.iters + { this };
    if node != null {
      l.list.list.LastHasLastIndex(node);
    }
  }

  constructor CopyCtr(it: LinkedListIteratorImpl<A>)
    modifies it.Parent()
    requires it.Valid()
    ensures it.Valid() 
    ensures it.Parent() == old(it.Parent())
    ensures it.Parent().Model() == old(it.Parent().Model())
    ensures it.Index() == old(it.Index())
    ensures Valid()
    ensures parent == it.parent
    ensures node == it.node
    ensures pastTheEnd == it.pastTheEnd

    ensures fresh(it.Parent().Repr() - old(it.Parent().Repr()))
    ensures it.Parent().Iterators() == {this} + old(it.Parent().Iterators())
    ensures forall it' | it' in old(it.Parent().Iterators()) && old(it'.Valid()) ::
      && it'.Valid() 
      && it'.Parent() == old(it'.Parent()) 
      && it'.Index() == old(it'.Index())
  {
    parent := it.parent;
    node := it.node;
    pastTheEnd := it.pastTheEnd;
    new;
    it.parent.iters := it.parent.iters + { this };
  }

  method HasPeek() returns (b: bool)
    modifies this, Parent(), Parent().Repr()
    requires allocated(Parent())
    requires allocated(Parent().Repr())
    ensures fresh(Parent().Repr() - old(Parent().Repr()))
    ensures allocated(Parent().Repr())

    requires Valid()
    requires Parent().Valid()
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Model() == old(Parent().Model())
    ensures Index() == old(Index())
    ensures b == HasPeek?()

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Index() == old(it.Index())
  {
    return node != null;
  }

  method Prev()
    modifies this, Parent(), Parent().Repr()
    requires allocated(Parent())
    requires allocated(Parent().Repr())
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures allocated(Parent().Repr())

    requires Valid()
    requires Parent().Valid()
    requires HasPeek?()
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Model() == old(Parent().Model())

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures Index() + 1 == old(Index())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && (it != this ==> it.Index() == old(it.Index()))
  {
    assert |parent.Model()| > 0;
    assert Index() >= 0;
    if Index() > 0 {
      assert parent.list.list.spine[Index()-1]
        == parent.list.list.spine[Index()].prev;
    }
    node := node.prev;
    pastTheEnd := false;
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
    ensures Parent().Valid()
    ensures Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Model() == old(Parent().Model())

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures Index() == 1 + old(Index())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && (it != this ==> it.Index() == old(it.Index()))
  {
    assert |parent.Model()| > 0;
    assert Index() < |parent.Model()|;
    if Index() < |parent.list.list.spine|-1 {
      assert parent.list.list.spine[Index()+1]
        == parent.list.list.spine[Index()].next;
    }
    node := node.next;
    pastTheEnd := true;
  }

  method Peek() returns (p: A)
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
    ensures Index() == old(Index())
    ensures p == Parent().Model()[Index()]

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Index() == old(it.Index())
  {
    return node.data;
  }

  method Copy() returns (it: ListIterator<A>)
    modifies this, Parent(), Parent().Repr()
    requires allocated(Parent())
    requires allocated(Parent().Repr())
    ensures fresh(Parent().Repr() - old(Parent().Repr()))
    ensures allocated(Parent().Repr())
    
    requires Valid()
    requires Parent().Valid()
    ensures fresh(it)
    ensures Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Valid()
    ensures Parent().Model() == old(Parent().Model())

    ensures it.Valid()
    ensures it in Parent().Iterators()
    ensures Parent().Iterators() >= {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()
    ensures Index() == it.Index()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      && it.Valid()
      && it.Parent() == old(it.Parent()) 
      && it.Index() == old(it.Index())
  {
    it := new LinkedListIteratorImpl.CopyCtr(this);
  }

  method Set(x: A)
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
    ensures |Parent().Model()| == old(|Parent().Model()|)
    ensures Index() == old(Index()) 
    ensures Parent().Model() == old(Parent().Model()[Index():=x])

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Index() == old(it.Index())
  {
    node.data := x;
  }
}

class LinkedListImpl<A> extends LinkedList<A> {
  var list: DoublyLinkedListWithLast<A>
  var size: nat
  ghost var iters: set<LinkedListIteratorImpl<A>>

  ghost function Repr0(): set<object>
    reads this
  {
    {list} + iters
  }

  ghost function Repr1(): set<object>
    reads this, Repr0()
  {
    Repr0() + {list.list}
  }

  ghost function Repr2(): set<object>
    reads this, Repr1()
  {
    Repr1() + list.Repr()
  }

  ghost function ReprFamily(n: nat): set<object>
    decreases n
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)
  {
    if n == 0 then
      Repr0()
    else if n == 1 then
      Repr1()
    else if n == 2 then
      Repr2()
    else
      ReprFamily(n-1)
  }

  ghost predicate Valid()
    reads this, Repr()
  {
    && ReprDepth == 2
    && assert ReprFamily(0) <= ReprFamily(2); true
    && size == |list.list.spine|
    && list.Valid()
    && (forall it | it in iters :: it.parent == this && {it} !! {this})
  }

  ghost function Model(): seq<A>
    reads this, Repr()
    requires Valid()
  {
    list.Model()
  }

  method Empty() returns (b: bool)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures b == Empty?()

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Index() == old(it.Index())
  {
    return list.list.head == null;
  }

  method Size() returns (s: nat)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures s == |Model()|

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Index() == old(it.Index())
  {
    assert Valid();
    assert size == |list.list.spine| == |list.list.Model()| == |list.Model()| == |Model()|;
    return size;
  }

  ghost function Iterators(): set<ListIterator<A>>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
  {
    iters
  }

  constructor()
    ensures fresh(Repr())
    ensures allocated(Repr())

    ensures Valid()
    ensures Model() == []
  {
    ReprDepth := 2;
    list := new DoublyLinkedListWithLast();
    size := 0;
    iters := {};
  }

  method First() returns (it: ListIterator<A>)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())

    ensures fresh(it)
    ensures Iterators() >= {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Index() == 0
    ensures it.Parent() == this
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent())
      && it.Index() == old(it.Index())
  {
    it := new LinkedListIteratorImpl.First(this);
  }

  method Last() returns (it: ListIterator<A>)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())

    ensures fresh(it)
    ensures Iterators() >= {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Index() == |Model()| - 1 == |old(Model())| - 1 //no es capaz de deducirlo si no lo ponemos
    ensures it.Parent() == this
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Index() == old(it.Index())
  {
    it := new LinkedListIteratorImpl.Last(this);
  }

  method Front() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[0]

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Index() == old(it.Index())
  {
    x := list.Front();
  }

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
      && it.Valid()
      && it.Parent() == old(it.Parent()) 
      && if old(it.Index()) == -1 then
            it.Index() == old(it.Index())
         else
            it.Index() == old(it.Index()) + 1
  {
    list.PushFront(x);
    size := size + 1;
  }

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
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.Index()) > 0 ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Index() + 1 == old(it.Index())
  {
    x := list.PopFront();
    size := size - 1;
  }

  method Back() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[|Model()| - 1]

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && it.Index() == old(it.Index())
  {
    x := list.Back();
  }

  method PushBack(x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
    ensures |Model()| == old(|Model()|) + 1
    
    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      && it.Valid()
      && it.Parent() == old(it.Parent()) 
      && if old(it.Index()) == old(|Model()|) then
            it.Index() == 1 + old(it.Index())
         else
            it.Index()== old(it.Index())
  {
    list.PushBack(x);
    size := size + 1;
  }

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
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.Index()) != old(|Model()|-1) ::
      && it.Valid()
      && it.Parent() == old(it.Parent()) 
      && if old(it.Index()) == old(|Model()|) then
            it.Index() + 1 == old(it.Index())
         else
            it.Index() == old(it.Index())
  {
    x := list.PopBack();
    size := size - 1;
  }

  method CoerceIter(it: ListIterator<A>) returns (itl:LinkedListIteratorImpl<A>)
    requires Valid()
    requires it in Iterators()
    ensures itl == it as LinkedListIteratorImpl<A>
  {
    itl := it as LinkedListIteratorImpl<A>;
  }

  // Insertion after mid
  method InsertAfter(mid: ListIterator<A>, x: A)
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
    ensures Model() == Seq.Insert(x, old(Model()), old(mid.Index())+1)
    
    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) :: 
      && it.Valid()
      && it.Parent() == old(it.Parent()) 
      && if old(it.Index()) <= old(mid.Index())  then
            it.Index() == old(it.Index())
         else
            it.Index() == old(it.Index()) + 1
  {
    list.InsertAfter((mid as LinkedListIteratorImpl<A>).node, x);
    size := size + 1;
  }

  // Insertion before mid
  method Insert(mid: ListIterator<A>, x: A) returns (newt: ListIterator<A>)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires mid.Valid()
    requires mid in Iterators()
    requires mid.Parent() == this
    requires mid.Index() >= 0
    ensures Valid()
    ensures Model() == Seq.Insert(x, old(Model()), old(mid.Index()))

    ensures fresh(newt)
    ensures Iterators() >= {newt} + old(Iterators())
    ensures newt.Valid()
    ensures newt.Parent() == this
    ensures newt.Index() == old(mid.Index())

    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent()) 
      && if old(it.Index()) < old(mid.Index())  then
            it.Index() == old(it.Index())
         else
            it.Index() == old(it.Index()) + 1
  {
    if (mid as LinkedListIteratorImpl<A>).node == null {
      /*GHOST*/
      assert mid.Index() == |list.list.spine|;

      PushBack(x);
      
      newt := new LinkedListIteratorImpl.Internal(this, list.last);      
      
      assert list.last != null;
      list.list.LastHasLastIndex(list.last);
      /*calc == {
        newt.Index();
        list.list.GetIndex(list.last);
        |list.list.spine|-1;
        old(|list.list.spine|);
        old(mid.Index());

      }*/
    } else {
      
      var node := (mid as LinkedListIteratorImpl<A>).node;
      list.InsertBefore(node, x);
      size := size + 1;
      newt := new LinkedListIteratorImpl.Internal(this, node.prev);
      
      assert newt.Index() == mid.Index() - 1 == old(mid.Index());
    }
  }

  // Deletion of mid
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
    ensures Iterators() >= {next} + old(Iterators())
    ensures next.Valid()
    ensures next.Parent() == this
    ensures next.Index() == old(mid.Index())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.Index()) != old(mid.Index()) ::
      && it.Valid() 
      && it.Parent() == old(it.Parent())
      && if old(it.Index()) < old(mid.Index()) then
            it.Index() == old(it.Index())
         else
            it.Index() == old(it.Index()) - 1
  {
    next := mid.Copy();
    var x := next.Peek();
    next.Next();
    list.Remove((mid as LinkedListIteratorImpl<A>).node);
    size := size - 1;
  }
}

}
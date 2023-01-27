include "../../../src/linear/layer2/LinkedList.dfy"
include "../../../src/linear/layer4/DoublyLinkedListWithLast.dfy"

class LinkedListIteratorImpl<A> extends ListIterator<A> {
  ghost var parent: LinkedListImpl<A>
  var node: DNode?<A>
  ghost var pastTheEnd: bool

  predicate Valid()
    reads this, parent, parent.Repr()
  {
    && parent.Valid()
    && (node != null ==> node in parent.list.list.spine)
  }

  function Parent(): List<A>
    reads this
  {
    parent
  }

  function Index(): int
    reads this, parent, parent.Repr()
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

  constructor(l: LinkedListImpl<A>, n: DNode?<A>)
    requires l.Valid() && n in l.list.list.spine
    ensures Valid()
    ensures parent == l
    ensures Index() == parent.list.list.GetIndex(n)
    ensures node == n
  {
    parent := l;
    node := n;
    pastTheEnd := false;
  }

  constructor First(l: LinkedListImpl<A>)
    requires l.Valid()
    ensures Valid()
    ensures parent == l
    ensures Index() == 0
    ensures node == l.list.list.head
  {
    parent := l;
    node := l.list.list.head;
    pastTheEnd := true;
  }

  constructor Last(l: LinkedListImpl<A>)
    requires l.Valid()
    ensures Valid()
    ensures parent == l
    ensures Index() == |l.Model()| - 1
    ensures node == l.list.last
  {
    parent := l;
    node := l.list.last;
    pastTheEnd := false;
    new;
    if node != null {
      l.list.list.LastHasLastIndex(node);
    }
  }

  constructor CopyCtr(it: LinkedListIteratorImpl<A>)
    requires it.Valid()
    ensures Valid()
    ensures parent == it.parent
    ensures node == it.node
    ensures pastTheEnd == it.pastTheEnd
  {
    parent := it.parent;
    node := it.node;
    pastTheEnd := it.pastTheEnd;
  }

  method HasPeek() returns (b: bool)
    modifies this, Parent(), Parent().Repr()
    requires allocated(Parent())
    requires allocated(Parent().Repr())

    requires Valid()
    requires Parent().Valid()
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Model() == old(Parent().Model())
    ensures Index() == old(Index())
    ensures b == HasPeek?()

    ensures fresh(Parent().Repr() - old(Parent().Repr()))
    ensures allocated(Parent().Repr())

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
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
      it.Valid() && it.Parent() == old(it.Parent()) && (it != this ==> it.Index() == old(it.Index()))

  method Next()
    modifies this
    requires Valid()
    requires Parent().Valid()
    requires HasPeek?()
    requires allocated(Parent())
    requires forall it | it in Parent().Iterators() :: allocated(it)
    ensures Parent().Valid()
    ensures Valid()
    ensures old(Parent()) == Parent()
    ensures old(Parent().Model()) == Parent().Model()

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr() - old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures Index() == 1 + old(Index())
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Index() == old(it.Index()))
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

    requires Valid()
    requires Parent().Valid()
    requires HasPeek?()
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Model() == old(Parent().Model())
    ensures Index() == old(Index())
    ensures p == Parent().Model()[Index()]

    ensures fresh(Parent().Repr() - old(Parent().Repr()))
    ensures allocated(Parent().Repr())

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
  {
    return node.data;
  }

  method Copy() returns (it: ListIterator<A>)
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
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures it.Valid()
    ensures it in Parent().Iterators()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()
    ensures Index() == it.Index()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())
    ensures Parent().Model() == old(Parent().Model())
  {
    it := new LinkedListIteratorImpl.CopyCtr(this);
    parent.iters := {it} + parent.iters;
  }

  method Set(x: A)
    modifies node
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Repr() :: allocated(it)
    requires HasPeek?()
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())
    ensures |Parent().Model()| == old(|Parent().Model()|)
    ensures Parent().Model()[old(Index())] == x
    ensures forall i | 0 <= i < |Parent().Model()| && i != Index() ::
      Parent().Model()[i] == old(Parent().Model()[i])

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    //ensures Index() == old(Index())
    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())
  {
    node.data := x;
  }
}

class LinkedListImpl<A> extends LinkedList<A> {
  var list: DoublyLinkedListWithLast<A>;
  var size: nat;
  ghost var iters: set<LinkedListIteratorImpl<A>>;

  function Repr0(): set<object>
    reads this
  {
    {list} + iters
  }

  function Repr1(): set<object>
    reads this, Repr0()
  {
    Repr0() + {list.list}
  }

  function Repr2(): set<object>
    reads this, Repr1()
  {
    Repr1() + list.Repr()
  }

  function ReprFamily(n: nat): set<object>
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

  predicate Valid()
    reads this, Repr()
  {
    && ReprDepth == 2
    && size == |list.list.spine|
    && list.Valid()
    && (forall it | it in iters :: it.parent == this && {it} !! {this})
  }

  function Model(): seq<A>
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
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
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
      it.Valid() && it.Parent()==old(it.Parent()) && it.Index() == old(it.Index())
  {
    assert Valid();
    assert size == |list.list.spine| == |list.list.Model()| == |list.Model()| == |Model()|;
    return size;
  }

  function Iterators(): set<ListIterator<A>>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
  {
    iters
  }

  constructor()
    ensures Valid()
    ensures Model() == []

    ensures forall x | x in Repr() :: fresh(x)
    ensures fresh(Repr())
    ensures forall x | x in Repr() :: allocated(x)
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
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
  {
    var it1 := new LinkedListIteratorImpl.First(this);
    iters := {it1} + iters;
    it := it1;
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
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())

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
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
  {
    return list.Front();
  }

  method PushFront(x: A)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)

    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      && it.Valid()
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
    requires Valid()
    requires Model() != []
    requires forall x | x in Repr() :: allocated(x)

    ensures Valid()
    ensures [x] + Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in Iterators() && old(it.Valid()) && old(it.Index()) > 0 ::
      it.Valid() && it.Index() + 1 == old(it.Index())
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
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
  {
    return list.Back();
  }

  method PushBack(x: A)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)

    ensures Valid()
    ensures Model() == old(Model()) + [x]

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in Iterators() && old(it.Valid()) ::
      && it.Valid()
      && if old(it.Index()) == old(|Model()|) then
          it.Index() == 1 + old(it.Index())
        else
          it.Index()== old(it.Index())
  {
    list.PushBack(x);
    /*GHOST*/ size := size + 1;
  }

  method PopBack() returns (x: A)
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
    ensures
      forall it | it in old(Iterators())
          && old(it.Valid())
          && old(it.Index()) != old(|Model()|-1) ::
        && it.Valid()
        && if old(it.Index()) == old(|Model()|) then
            it.Index() + 1 == old(it.Index())
          else
            it.Index() == old(it.Index())
  {
    x := list.PopBack();
    /*GHOST*/ size := size - 1;
  }

  function method CoerceIter(it: ListIterator<A>): LinkedListIteratorImpl<A>
    reads this, Repr()
    requires Valid()
    requires it in Iterators()
    ensures it == CoerceIter(it)
  {
    it
  }

  // Insertion after mid
  method InsertAfter(mid: ListIterator<A>, x: A)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasPeek?()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == Seq.Insert(x, old(Model()), old(mid.Index())+1)
    ensures Iterators() == old(Iterators())
    ensures forall it | it in Iterators() && old(it.Valid()) :: it.Valid()
    ensures forall it | it in Iterators() && old(it.Valid()) ::
      if old(it.Index()) <= old(mid.Index())  then
        it.Index() == old(it.Index())
      else
        it.Index() == old(it.Index()) + 1
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    list.InsertAfter(CoerceIter(mid).node, x);
    size := size + 1;
  }

  // Insertion before mid
  method Insert(mid: ListIterator<A>, x: A) returns (newt: ListIterator<A>)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid in Iterators()
    requires mid.Parent() == this
    requires mid.Index() >= 0
    ensures Valid()
    ensures Model() == Seq.Insert(x, old(Model()), old(mid.Index()))

    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    ensures fresh(newt)
    ensures Iterators() == {newt} + old(Iterators())
    ensures newt.Valid()
    ensures newt.Parent() == this
    ensures newt.Index() == old(mid.Index())

    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() &&
      if old(it.Index()) < old(mid.Index())  then
        it.Index() == old(it.Index())
      else
        it.Index() == old(it.Index()) + 1
  {
    if CoerceIter(mid).node == null {
      /*GHOST*/
      assert mid.Index() == |list.list.spine|;
      PushBack(x);
      newt := new LinkedListIteratorImpl(this, list.last);

      assert list.last != null;
      list.list.LastHasLastIndex(list.last);
      calc == {
        newt.Index();
        list.list.GetIndex(list.last);
        |list.list.spine|-1;
        old(|list.list.spine|);
        old(mid.Index());

      }
      assert forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x);
    } else {
      var node := CoerceIter(mid).node;
      list.InsertBefore(node, x);
      size := size + 1;
      newt := new LinkedListIteratorImpl(this, node.prev);

      assert newt.Index() == mid.Index() - 1 == old(mid.Index());
      assert fresh(newt);
      assert fresh(Repr()-old(Repr()));
      assert allocated(Repr());
      assert Valid();
      assert Model() == Seq.Insert(x, old(Model()), old(mid.Index()));
      assert newt.Valid();
      assert newt.Parent() == this;
    }
    assert fresh(newt);
    iters := {newt} + iters;
  }

  // Deletion of mid
  method Erase(mid: ListIterator<A>) returns (next: ListIterator<A>)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasPeek?()
    requires mid in Iterators()
    ensures Valid()
    ensures Model() == Seq.Remove(old(Model()), old(mid.Index()))

    requires allocated(Repr())
    ensures fresh(Repr()-old(Repr()))
    ensures allocated(Repr())

    ensures fresh(next)
    ensures Iterators() >= {next} + old(Iterators())
    ensures next.Valid()
    ensures next.Parent() == this
    ensures next.Index() == old(mid.Index())
    ensures forall it |
        && it in old(Iterators())
        && old(it.Valid())
        && old(it.Index()) != old(mid.Index()) ::
      it.Valid() &&
      if old(it.Index()) < old(mid.Index()) then
        it.Index() == old(it.Index())
      else
        it.Index() == old(it.Index()) - 1
  {
    next := mid.Copy();
    var x := next.Peek();
    next.Next();
    list.Remove(CoerceIter(mid).node);
    size := size - 1;
    iters := {next} + iters;
  }
}

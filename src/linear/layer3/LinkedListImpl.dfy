include "../../../src/linear/layer2/LinkedList.dfy"
include "../../../src/linear/layer4/DoublyLinkedListWithLast.dfy"

class ListIterator1 extends ListIterator {
  ghost var parent: List1
  var node: DNode?

  predicate Valid()
    reads this, parent, parent.Repr()
  {
    && parent.Valid()
    && (node != null ==> node in parent.list.list.spine)
  }

  function Parent(): List
    reads this
  {
    parent
  }

  function Index(): nat
    reads this, parent, parent.Repr()
    requires Valid()
    requires Parent().Valid()
    ensures Index() <= |Parent().Model()|
  {
    if node != null then
      parent.list.list.GetIndex(node)
    else
      parent.list.list.ModelRelationWithSpine();
      |parent.list.list.spine|
  }

  constructor(l: List1, n: DNode?)
    requires l.Valid()
    ensures Valid()
    ensures parent == l
    ensures Index() == 0
    ensures node == l.list.list.head
  {
    parent := l;
    node := n;
  }

  constructor Begin(l: List1)
    requires l.Valid()
    ensures Valid()
    ensures parent == l
    ensures Index() == 0
    ensures node == l.list.list.head
  {
    parent := l;
    node := l.list.list.head;
  }

  constructor CopyCtr(it: ListIterator1)
    requires it.Valid()
    ensures Valid()
    ensures parent == it.parent
    ensures node == it.node
  {
    parent := it.parent;
    node := it.node;
  }

  function method HasNext(): bool
    reads this
  {
    node != null
  }

  method Next() returns (x: int)
    modifies this
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    requires allocated(Parent())
    requires forall it | it in Parent().Iterators() :: allocated(it)
    ensures Parent().Valid()
    ensures Valid()
    ensures old(Index()) < Index()
    ensures old(Parent()) == Parent()
    ensures old(Index()) < |Parent().Model()|
    ensures old(Parent().Model()) == Parent().Model()
    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures x == Parent().Model()[old(Index())]
    ensures Index() == 1 + old(Index())
    ensures forall it | it in Parent().Iterators() && old(it.Valid()) ::
      it.Valid() && (it != this ==> it.Index() == old(it.Index()))
    ensures forall x | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures forall x | x in Parent().Repr() :: allocated(x)
  {
    assert |parent.Model()| > 0;
    assert Index() < |parent.Model()|;
    { // GHOST
      parent.list.list.ModelRelationWithSpine();
      if Index() < |parent.list.list.spine|-1 {
        assert parent.list.list.spine[Index()+1]
          == parent.list.list.spine[Index()].next;
      }
    }
    x := node.data;
    node := node.next;
  }

  function method Peek(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() == Parent().Model()[Index()]
  {
    parent.list.list.ModelRelationWithSpine();
    node.data
  }

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
    ensures it in Parent().Iterators()
    ensures Parent().Iterators() == {it} + old(Parent().Iterators())
    ensures Parent() == old(Parent())
    ensures Parent() == it.Parent()
    ensures Index() == it.Index()
    ensures it.Valid()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())
    ensures Parent().Model() == old(Parent().Model())
    ensures forall x | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures forall x | x in Parent().Repr() :: allocated(x)
  {
    it := new ListIterator1.CopyCtr(this);
    parent.iters := {it} + parent.iters;
  }

  method Set(x: int)
    modifies node
    requires Valid()
    requires Parent().Valid()
    requires allocated(Parent())
    requires forall it | it in Parent().Repr() :: allocated(it)
    requires HasNext()
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())

    ensures forall x {:trigger x in Parent().Repr(), x in old(Parent().Repr())} | x in Parent().Repr() - old(Parent().Repr()) :: fresh(x)
    ensures fresh(Parent().Repr()-old(Parent().Repr()))
    ensures forall x | x in Parent().Repr() :: allocated(x)

    ensures Parent().Iterators() == old(Parent().Iterators())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index())
    ensures |Parent().Model()| == old(|Parent().Model()|)
    ensures Index() == old(Index())
    ensures Parent().Model()[Index()] == x
    ensures forall i | 0 <= i < |Parent().Model()| && i != Index() ::
      Parent().Model()[i] == old(Parent().Model()[i])
  {
    parent.list.list.ModelRelationWithSpine();
    node.data := x;
    parent.list.list.ModelRelationWithSpine();
  }
}

class List1 extends LinkedList {
  var list: DoublyLinkedListWithLast;
  var size: nat;
  ghost var iters: set<ListIterator1>;

  function ReprDepth(): nat
    ensures ReprDepth() > 0
  {
    2
  }

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
    requires n <= ReprDepth()
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
      assert false;
      {}
  }

  lemma UselessLemma()
    ensures Repr() == ReprFamily(ReprDepth());
  {}

  predicate Valid()
    reads this, Repr()
  {
    && size == |list.list.spine|
    && list.Valid()
    && forall it | it in iters :: it.parent == this && {it} !! {this}
  }

  function Model(): seq<int>
    reads this, Repr()
    requires Valid()
  {
    list.Model()
  }

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []
  {
    list.list.head == null
  }

  function method Size(): nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|
  {
    list.list.ModelRelationWithSpine();
    assert Valid();
    assert size == |list.list.spine| == |list.list.Model()| == |list.Model()| == |Model()|;
    size
  }

  function Iterators(): set<ListIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
  {
    iters
  }

  method Begin() returns (it: ListIterator)
    modifies this, Repr()
    requires Valid()
    // requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model())
    ensures fresh(it)
    ensures Iterators() == {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Index() == 0
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    var it1 := new ListIterator1.Begin(this);
    iters := {it1} + iters;
    it := it1;
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures forall x | x in Repr() :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    list := new DoublyLinkedListWithLast();
    size := 0;
    iters := {};
  }

  function method Front(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Front() == Model()[0]
  {
    list.Front()
  }

  method PushFront(x: int)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in Iterators() && old(it.Valid()) ::
      it.Valid() && it.Index() == old(it.Index()) + 1
  {
    list.PushFront(x);
    /*GHOST*/ size := size + 1;
    /*GHOST*/ list.list.ModelRelationWithSpine();
  }

  method PopFront() returns (x: int)
    modifies this, Repr()
    requires Valid()
    requires Model() != []
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures [x] + Model() == old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures forall it | it in Iterators() && old(it.Valid()) && old(it.Index()) != 0 ::
      it.Valid() && it.Index() + 1 == old(it.Index())
  {
    x := list.PopFront();
    /*GHOST*/ size := size - 1;
    /*GHOST*/ list.list.ModelRelationWithSpine();
  }

  function method Back(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Back() == Model()[|Model()|-1]
  {
    list.Back()
  }

  method PushBack(x: int)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == old(Model()) + [x]

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
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
    /*GHOST*/ list.list.ModelRelationWithSpine();
  }

  method PopBack() returns (x: int)
    modifies this, Repr()
    requires Valid()
    requires Model() != []
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() + [x] == old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures
      forall it |
          && it in Iterators()
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
    /*GHOST*/ list.list.ModelRelationWithSpine();
  }

  function method CoerceIter(it: ListIterator): ListIterator1
    reads this, Repr()
    requires Valid()
    requires it in Iterators()
    ensures it == CoerceIter(it)
  {
    it
  }

  // Insertion after mid
  method InsertAfter(mid: ListIterator, x: int)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
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
  method Insert(mid: ListIterator, x: int) returns (newt: ListIterator)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid in Iterators()
    requires mid.Parent() == this
    requires forall x | x in Repr() :: allocated(x)
    ensures Valid()
    ensures Model() == Seq.Insert(x, old(Model()), old(mid.Index()))

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

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
    // newt := mid;
    // assert newt.Valid();
    if CoerceIter(mid).node == null {
      assert mid.Index() == |list.list.spine|;
      list.list.ModelRelationWithSpine();
      PushBack(x);
      newt := new ListIterator1(this, list.last);
      assert list.last != null;
      list.list.LastHasLastIndex(list.last);
      calc == {
        newt.Index();
        list.list.GetIndex(list.last);
        |list.list.spine|-1;
        old(|list.list.spine|);
        old(mid.Index());
      }
    } else {
      var node := CoerceIter(mid).node;
      list.InsertBefore(node, x);
      size := size + 1;
      newt := new ListIterator1(this, node.prev);
      // assert newt.Index() + 1 == mid.Index();
      assert newt.Index() == mid.Index() - 1 == old(mid.Index());
    }
    iters := {newt} + iters;
  }

  // Deletion of mid
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
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(next)
    ensures Iterators() == {next} + old(Iterators())
    ensures next.Valid()
    ensures next.Parent() == this
    ensures next.Index()==old(mid.Index())
    ensures forall it |
        && it in old(Iterators())
        && old(it.Valid())
        && old(it.Index()) != old(mid.Index()) ::
      it.Valid() &&
      if old(it.Index()) < old(mid.Index())  then
        it.Index() == old(it.Index())
      else
        it.Index() == old(it.Index()) - 1
  {
    next := mid.Copy();
    var x := next.Next();
    list.Remove(CoerceIter(mid).node);
    size := size - 1;
  }
}

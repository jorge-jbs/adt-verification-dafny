include "../../../src/linear/aux/DoublyLinkedListWithLast.dfy"
include "../../../src/linear/impl/LinkedList.dfy"

class ListIterator1 extends LinkedListIterator {
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

  constructor(l: List1)
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
    var it1 := new ListIterator1(this);
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

    ensures iters == old(iters)
    ensures forall it | it in Iterators() && old(it.Valid()) ::
      it.Valid() // && it.Index() == old(it.Index()) + 1
  {
    /*GHOST*/ list.list.ModelRelationWithSpine();
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

    ensures iters == old(iters)
    ensures forall it | it in iters && old(it.Valid()) ::
      if old(it.Index()) == 0 then
        !it.Valid()
      else
        it.Valid() // && it.Index() + 1 == old(it.Index())
  {
    /*GHOST*/ list.list.ModelRelationWithSpine();
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

    ensures iters == old(iters)
    ensures forall it | it in iters && old(it.Valid()) ::
      it.Valid() // && it.Index() == old(it.Index())
  {
    /*GHOST*/ list.list.ModelRelationWithSpine();
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

    ensures iters == old(iters)
    ensures forall it | it in iters && old(it.Valid()) ::
      if old(it.Index()) == old(|Model()|-1)  then
        !it.Valid()
      else if old(it.Index()) == old(|Model()|) then
        it.Valid() && it.Index() + 1 == old(it.Index())
      else
        it.Valid() && it.Index() == old(it.Index())
  {
    x := list.PopBack();
    /*GHOST*/ size := size - 1;
    /*GHOST*/ list.list.ModelRelationWithSpine();
  }

  function method {:axiom} CoerceIter(it: ListIterator): ListIterator1
    reads this, Repr()
    requires Valid()
    requires it in Iterators()
    ensures it == CoerceIter(it)

  method Insert(mid: ListIterator, x: int)
    modifies this, Repr()
    requires Valid()
    requires mid.Valid()
    requires mid.Parent() == this
    requires mid.HasNext()
    requires mid in Iterators()
    requires forall x | x in Repr() :: allocated(x)
    requires mid.Index() < |Model()|
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
    list.Insert(CoerceIter(mid).node, x);
    size := size + 1;
  }
}

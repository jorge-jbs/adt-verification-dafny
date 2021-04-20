include "../../../src/linear/implementation/DoublyLinkedListWithLast.dfy"
include "../../../src/linear/interface/List2.dfy"

class ListIterator1 extends ListIterator {
  ghost var index: nat
  ghost var parent: List1
  var node: DNode?

  predicate Valid()
    reads this, parent, parent.Repr()
  {
    && parent.Valid()
    && ( node != null ==>
          && node in parent.list.list.Repr()
          && index == parent.list.list.GetIndex(node)
      )
  }

  function Parent(): List
    reads this
  {
    parent
  }

  function Index(): nat
    reads this //, Parent(), Parent().Repr()
    // requires Parent().Valid()
    // ensures Index() < |Parent().Model()|
  {
    index
  }

  constructor(l: List1)
    requires l.Valid()
    ensures Valid()
    ensures parent == l
    ensures index == 0
    ensures node == l.list.list.head
  {
    index := 0;
    parent := l;
    node := l.list.list.head;
  }

  function method HasNext(): bool
    reads this
  {
    node != null
  }

  method Next() returns (x: int)
    modifies this
    requires {this} !! {Parent()} + Parent().Repr()
    requires Parent().Valid()
    requires this in Parent().ValidIterators()
    requires HasNext()
    requires |Parent().Model()| > 0
    ensures Parent().Valid()
    ensures this in Parent().ValidIterators()
    ensures old(Index()) < Index()
    ensures old(Parent()) == Parent()
    ensures old(Index()) < |Parent().Model()|
    ensures x == Parent().Model()[old(Index())]
    ensures Index() == 1 + old(Index())
  {
    assert index < |parent.Model()|;
    { // GHOST
      parent.list.list.ModelRelationWithSpine();
      if index < |parent.list.list.spine|-1 {
        assert parent.list.list.spine[index+1]
          == parent.list.list.spine[index].next;
      }
    }
    x := node.data;
    index := index + 1;
    node := node.next;
  }
}

class List1 extends List {
  var list: DoublyLinkedListWithLast;
  var size: nat;
  ghost var iters: set<ListIterator1>;
  ghost var validIters: set<ListIterator1>;

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
    && validIters <= iters
    && list.Valid()
    && forall it | it in iters :: it.Parent() == this && {it} !! {this}
    && forall it | it in validIters :: it.node in list.list.spine
  }

  function Iterators(): set<ListIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() ::
      && it.Parent() == this
      && {it} !! {this} + Repr()
  {
    iters
  }

  function ValidIterators(): set<ListIterator>
    reads this, Repr()
    requires Valid()
    ensures ValidIterators() <= Iterators()
  {
    // assert ValidIterators() == validIters <= iters == Iterators();
    validIters
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

  method GetIterator() returns (it: ListIterator)
    modifies this, Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures Iterators() == {it} + old(Iterators())
    // ensures it !in old(Iterators())
    // ensures it in Iterators()
    ensures it.Index() == 0
    // ensures ValidIterator(it)
    // ensures it.Valid()
    ensures fresh(it)
    ensures it in ValidIterators()
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    var it1 := new ListIterator1(this);
    // assert it1.Parent() == it1.parent == this;
    // assert forall it: ListIterator1 | it in iters ::
    //   it.Parent() == this && {it} !! {this} + Repr();
    // assert it1.Parent() == this && {it1} !! {this} + Repr();
    // assert forall it: ListIterator1 | it in ({it1} + iters) ::
    //   it.Parent() == this && {it} !! {this} + Repr();
    // assert iters == old(iters);
    // assert forall it: ListIterator1 | it in ({it1} + old(iters)) ::
    //   it.Parent() == this && {it} !! {this} + Repr();
    iters := {it1} + iters;
    // assert iters == {it1} + old(iters);
    // assert forall it: ListIterator1 | it in old(iters) ::
    //   it.Parent() == this && {it} !! {this} + Repr();
    // assert it1.Parent() == this && {it1} !! {this} + Repr();
    // assert forall it: ListIterator1 | it == it1 || it in old(iters) ::
    //   it.Parent() == this && {it} !! {this} + Repr();
    // assert forall it: ListIterator1 | it in ({it1} + old(iters)) ::
    //   it.Parent() == this && {it} !! {this} + Repr();
    // assert forall it: ListIterator1 | it in iters ::
    //   it.Parent() == this && {it} !! {this} + Repr();
    validIters := {it1} + validIters;
    it := it1;
    // assert forall it | it in iters :: it.Parent() == this && {it} !! {this} + Repr();
    // assert it.Parent() == this;
  }

  /*
  method IAt(it: ListIterator) returns (x: int)
    requires Valid()
    requires it.Parent() == this
    requires {it} !! {this}
    requires it.Index() < |Model()|
    requires it in ValidIterators()

    ensures Valid()
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    ensures it.Index() == old(it.Index())
    ensures it.Parent() == old(it.Parent())
    ensures Model() == old(Model())

    ensures x == Model()[it.Index()]
  {
    // var it1 :| it1 in validIters && it1 == it;
    assert it in validIters;
    // x := it.node.data;
  }
  */

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures forall x | x in Repr() :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    list := new DoublyLinkedListWithLast();
    size := 0;
    iters := {};
    validIters := {};
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
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
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
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
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
    ensures Valid()
    ensures Model() == old(Model()) + [x]
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
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
    ensures Valid()
    ensures Model() + [x] == old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == old(Iterators())
    ensures ValidIterators() <= old(ValidIterators())
    ensures forall it | it in Iterators() && it in old(ValidIterators()) ::
      if it.Index() == old(|Model()|-1) then
        it !in ValidIterators()
      else
        it in ValidIterators()
  {
    /*GHOST*/ list.list.ModelRelationWithSpine();
    x := list.PopBack();
    /*GHOST*/ size := size - 1;
    /*GHOST*/ list.list.ModelRelationWithSpine();
    assert forall it | it in iters && it in old(validIters) ::
      it.Index() != old(|Model()|-1);
    assert forall it | it in Iterators() && it in old(ValidIterators()) ::
      it.Index() != old(|Model()|-1);
  }
}

/*
class QueueIterator {
  ghost var index: nat
  ghost var parent: Queue1
  var node: DNode?

  predicate Valid()
    reads this, parent, parent.Repr()
  {
    && parent.Valid()
    && ( node != null ==>
          && node in parent.list.list.Repr()
          && index == parent.list.list.GetIndex(node)
      )
  }

  constructor(l: Queue1)
    requires l.Valid()
    ensures Valid()
    ensures parent == l
  {
    index := 0;
    parent := l;
    node := l.list.list.head;
  }

  function method HasNext(): bool
    reads this
  {
    node != null
  }

  method Next() returns (x: int)
    modifies this
    requires HasNext()
    requires Valid()
    ensures Valid()
    ensures x == old(parent.Model()[index])
    ensures old(index) < index
    ensures parent == old(parent)
  {
    { // GHOST
      parent.list.list.ModelRelationWithSpine();
      if index < |parent.list.list.spine|-1 {
        assert parent.list.list.spine[index+1]
          == parent.list.list.spine[index].next;
      }
    }
    x := node.data;
    index := index + 1;
    node := node.next;
  }
}
   */

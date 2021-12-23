include "../../Utils.dfy"
include "Vector.dfy"

class ArrayListIteratorImpl extends ArrayListIterator {
  var parent: ArrayListImpl
  var index: nat

  predicate Valid()
    reads this, parent, parent.Repr()
  {
    parent.Valid()
    && 0 <= index <= parent.size
  }

  function Parent(): List
    reads this
  {
    parent
  }

  function Index() : nat
    reads this, parent, parent.Repr()
    requires Valid()
    requires Parent().Valid()
    ensures Index() <= |Parent().Model()|
  {
    index
  }

  constructor(vector: ArrayListImpl)
    requires vector.Valid()
    ensures Valid()
    ensures Parent() == vector
    ensures Index() == 0
  {
    this.parent := vector;
    this.index := 0;
  }

  function method HasNext(): bool
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures HasNext() <==> Index() < |Parent().Model()|
  {
    index < parent.size
  }

  function method Peek(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    requires HasNext()
    ensures Peek() == Parent().Model()[Index()]
  {
    parent.elements[index]
  }

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
    {
      var elem := parent.elements[index];
      index := index + 1;
      return elem;
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
    {
      var itImpl := new ArrayListIteratorImpl(parent);
      itImpl.index := index;
      it := itImpl;
      parent.iterators := parent.iterators + { itImpl };
    }

  method Set(x: int)
    modifies Parent(), Parent().Repr()
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
    parent.elements[index] := x;
  }
}

class ArrayListImpl extends ArrayList {
  var elements: array<int>;
  var size: nat;
  ghost var iterators: set<ArrayListIteratorImpl>

  lemma UselessLemma()
    ensures Repr() == ReprFamily(ReprDepth());

  function ReprDepth(): nat
  {
    1
  }

  function Repr0(): set<object>
    reads this
  {
    {this, elements} + iterators
  }

  function ReprFamily(n: nat): set<object>
    decreases n
    requires n <= ReprDepth()
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
    reads this, if n == 0 then {} else ReprFamily(n-1)
  {
    if n == 0 then
      Repr0()
    else
      ReprFamily(n-1)
  }

  predicate Valid()
    reads this, Repr()
  {
    0 <= size <= elements.Length
      && elements.Length >= 1
      && forall it | it in iterators :: it.parent == this
  }

  function Model(): seq<int>
    reads this, Repr()
    requires Valid()
  {
    elements[..size]
  }

  function Iterators(): set<ListIterator>
    reads this, Repr()
    requires Valid()
    ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
  {
    iterators
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    elements := new int[1];
    size := 0;
    iterators := {};
  }

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []
  {
    size == 0
  }

  function method Size(): nat
    reads this, Repr()
    requires Valid()
    ensures Size() == |Model()|
  {
    size
  }

  function method Front(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []

    ensures Valid()
    ensures Front() == Model()[0]
  {
    elements[0]
  }

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
    ensures forall it | it in old(iterators) :: old(it.Valid())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();
  {
    if (size == elements.Length) {
      Grow(elements.Length * 2);
    }
    assert size < elements.Length;
    ShiftRight(0);
    elements[0] := x;
    size := size + 1;
  }

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
    ensures forall it | it in old(iterators) :: old(it.Valid()) && old(it.HasNext())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();
  {
    x := elements[0];
    ShiftLeft(0);
    size := size - 1;
  }

  function method Back(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []

    ensures Valid()
    ensures Back() == Model()[|Model()|-1]
  {
    elements[size - 1]
  }

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
    ensures forall it | it in old(iterators) :: old(it.Valid()) && old(it.HasNext())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();
  {
    assert size > 0;
    x := elements[size - 1];
    size := size - 1;
  }

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
    ensures forall it | it in old(iterators) :: old(it.Valid())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();
  {
    if (size == elements.Length) {
      Grow(elements.Length * 2);
    }
    assert size < elements.Length;
    elements[size] := x;
    size := size + 1;
  }

  method Begin() returns (it: ListIterator)
    modifies this, Repr()
    requires Valid()
    requires forall x | x in Repr()::allocated(x)

    ensures Valid()
    ensures Model() == old(Model())

    ensures fresh(it)
    ensures it.Valid()
    ensures it.Parent() == this
    ensures it.Index() == 0

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures Iterators() == {it} + old(Iterators())
    ensures forall it | it in old(iterators) :: old(it.Valid())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();
  {
    it := new ArrayListIteratorImpl(this);
    iterators := iterators + { it };
  }

  // Insertion before mid
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
    ensures forall it | it in old(iterators) :: old(it.Valid())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();
  {
    var midImpl := mid as ArrayListIteratorImpl;
    if (size == elements.Length) {
      Grow(elements.Length * 2);
    }
    assert size < elements.Length;
    assert Model() == old(Model());
    ShiftRight(midImpl.index);
    elements[midImpl.index] := x;
    size := size + 1;
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
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)

    ensures fresh(next)
    ensures Iterators() == {next} + old(Iterators())
    ensures forall it | it in old(iterators) :: old(it.Valid()) && old(it.HasNext())
      ==> it.Valid() && old(it.Parent()) == it.Parent() && old(it.Index()) == it.Index();
    ensures next.Valid() && next.Parent() == this && next.Index() == mid.Index();
  {
    var midImpl := mid as ArrayListIteratorImpl;
    assert midImpl.index == mid.Index();
    ShiftLeft(midImpl.index);
    assert forall j | midImpl.index <= j < size - 1 :: elements[j] == old(elements[j + 1]);
    assert forall j | 0 <= j < midImpl.index :: elements[j] == old(elements[j]);

    assert elements[..midImpl.index] == old(elements[0..midImpl.index]);
    assert elements[midImpl.index..size - 1] == old(elements[midImpl.index + 1..size]);

    // assert Seq.Remove(old(elements[..size]), midImpl.index)
    //         == old(elements[..size])[..midImpl.index] + old(elements[..size])[midImpl.index + 1..size]
    //         == elements[..midImpl.index] + old(elements[..size])[midImpl.index + 1..]
    //         == elements[..midImpl.index] + elements[midImpl.index..size - 1]
    //         == elements[..size - 1];

    // assert elements[..size - 1] == Seq.Remove(old(elements[..size]), midImpl.index);
    size := size - 1;
    // assert elements[..size] == Seq.Remove(old(elements[..size]), midImpl.index);
    // assert Model() == Seq.Remove(old(Model()), midImpl.index);
    next := midImpl.Copy();
    iterators := iterators + { next };
  }

  method Grow(newCapacity: nat)
    modifies this
    requires newCapacity >= elements.Length
    requires Valid()
    requires forall x | x in Repr() :: allocated(x)

    ensures Valid()
    ensures Model() == old(Model())
    ensures this.elements.Length == newCapacity

    ensures Iterators() == old(Iterators())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    var newElements := new int[newCapacity];
    var i := 0;
    while (i < size)
      invariant elements == old(elements)
      invariant size == old(size)
      invariant 0 <= i <= size <= elements.Length <= newElements.Length
      invariant newElements[..i] == elements[..i]
      invariant newElements[..i] == old(elements)[..i]
      invariant iterators == old(iterators)
    {
      newElements[i] := elements[i];
      i := i + 1;
    }

    elements := newElements;
  }

  method ShiftRight(from: nat)
    requires 0 <= from <= size < elements.Length
    modifies this.elements
    requires Valid()
    ensures forall j | 0 <= j < from :: elements[j] == old(elements[j]);
    ensures forall j | from < j <= size :: elements[j] == old(elements[j - 1]);
    ensures Valid()
  {
    ghost var oldElems := elements[..];
    assert oldElems[..] == old(elements)[..];

    var i := size;
    while (i > from)
      invariant from <= i <= size
      invariant forall j | 0 <= j < i :: elements[j] == oldElems[j]
      invariant forall j | i < j <= size :: elements[j] == oldElems[j - 1]
      modifies this.elements
    {
      elements[i] := elements[i - 1];
      i := i - 1;
    }
  }

  method ShiftLeft(until: nat)
    requires 0 <= until < size <= elements.Length
    requires Valid()
    ensures forall j | until <= j < size - 1 :: elements[j] == old(elements[j + 1]);
    ensures forall j | 0 <= j < until :: elements[j] == old(elements[j]);
    ensures Valid()
    modifies this.elements
  {
    ghost var oldElems := elements[..];
    assert oldElems[..] == old(elements)[..];

    var i := until;
    while (i < size - 1)
      invariant until <= i < size
      invariant forall j | until <= j < i :: elements[j] == oldElems[j + 1]
      invariant forall j | i <= j < size :: elements[j] == oldElems[j]
      invariant forall j | 0 <= j < until :: elements[j] == oldElems[j]
      modifies this.elements
    {
      elements[i] := elements[i + 1];
      i := i + 1;
    }
    assert i == size - 1;
  }
}

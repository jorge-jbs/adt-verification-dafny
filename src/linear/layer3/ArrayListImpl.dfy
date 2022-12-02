include "../../../src/linear/layer2/ArrayList.dfy"
include "../../../src/Utils.dfy"

class ArrayListIteratorImpl<A> extends ListIterator<A> {
  var parent: ArrayListImpl<A>
  var index: int

  function Parent(): List<A>
    reads this
  { parent }

  predicate Valid()
    reads this, Parent(), Parent().Repr()
    ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()
  {
    Parent().Valid()
    && this in Parent().Iterators()
    && -1 <= index <= parent.size
  }

  function Index(): int
    reads this, Parent(), Parent().Repr()
    requires Valid()
    requires Parent().Valid()
    ensures -1 <= Index() <= |Parent().Model()|
  { index }

  constructor(parent: ArrayListImpl<A>, index: int)
    modifies parent
    requires parent.Valid()
    requires -1 <= index <= |parent.Model()|
    ensures Valid()
    ensures Parent() == parent
    ensures Index() == index
    ensures parent.iterators == old(parent.iterators) + { this }
    ensures parent.Model() == old(parent.Model())
    ensures fresh(parent.Repr() - old(parent.Repr()))
  {
    this.parent := parent;
    this.index := index;
    new;
    this.parent.iterators := this.parent.iterators + { this };
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
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
  {
    b := 0 <= index < parent.size;
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
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
  {
    p := parent.elements[index];
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
    ensures Valid()
    ensures Parent().Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Model() == old(Parent().Model())

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures Index() == 1 + old(Index())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent() == old(it.Parent()) && (it != this ==> it.Index() == old(it.Index()))
    {
      index := index + 1;
    }

  method Prev() 
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

    ensures Parent().Iterators() >= old(Parent().Iterators())
    ensures Index() + 1 == old(Index())
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent() == old(it.Parent()) && (it != this ==> it.Index() == old(it.Index()))
  {
    index := index - 1;
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
    ensures Parent().Valid()
    ensures Parent() == old(Parent())
    ensures Parent().Model() == old(Parent().Model())
    ensures Index() == old(Index())
    
    ensures it.Valid()
    ensures Parent().Iterators() >= {it} + old(Parent().Iterators())
    ensures Parent() == it.Parent()
    ensures Index() == it.Index()
    ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
    {
      var itImpl := new ArrayListIteratorImpl(parent, index);      
      it := itImpl; 
      parent.iterators := parent.iterators + { itImpl };
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
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
 {
    parent.elements[index] := x;
  }
}

class ArrayListImpl<A> extends ArrayList<A> {
  var elements: array<A>;
  var size: nat;
  ghost var iterators: set<ArrayListIteratorImpl<A>>

  function Repr0(): set<object>
    reads this
  {
    {this, elements} + iterators
  }

  function ReprFamily(n: nat): set<object>
    decreases n
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
    && ReprDepth == 1
    && 0 <= size <= elements.Length
    && elements.Length >= 0
    && forall it | it in iterators :: it.parent == this
  }

  function Model(): seq<A>
    reads this, Repr()
    requires Valid()
  {
    elements[..size]
  }

  function Iterators(): set<ListIterator<A>>
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
    ensures forall x | x in Repr() :: fresh(x)
  {
    ReprDepth := 1;
    elements := new A[0];
    size := 0;
    iterators := {};
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
  {
    b := size == 0;
  }

  method Size() returns (s: nat)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())
    
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())
    ensures s == |Model()|

    ensures Iterators() >= old(Iterators())
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
  {
    s := size;
  }

  method Front() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[0]

    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())
 
    ensures Iterators() >= old(Iterators())
  {
    x := elements[0];
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
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
  {      
    if (size == elements.Length) {
      Grow(elements.Length * 2 + 1, x);
    }
    assert size < elements.Length;
    ShiftRight(0);
    elements[0] := x;
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
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasPeek?())
      :: it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
  {
    x := elements[0];
    ShiftLeft(0);
    size := size - 1;
  }

  method Back() returns (x: A)//Nuevo metodo
    modifies this, Repr()
    requires allocated(Repr())
    
    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[|Model()| - 1]

    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())
 
    ensures Iterators() >= old(Iterators())
  {
    x := elements[size - 1];
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
    ensures forall it | it in old(Iterators()) && old(it.Valid()) && old(it.HasPeek?())
      :: it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
  {
    assert size > 0;
    x := elements[size - 1];
    size := size - 1;
  }

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
  {
    if (size == elements.Length) {
      Grow(elements.Length * 2 + 1, x);
    }
    assert size < elements.Length;
    elements[size] := x;
    size := size + 1;
  }

  method First() returns (it: ListIterator<A>)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
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
    it := new ArrayListIteratorImpl(this, 0);
    iterators := iterators + { it };
  }

  method Last() returns (it: ListIterator<A>)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())
 
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model())

    ensures fresh(it)
    ensures Iterators() >= {it} + old(Iterators())
    ensures it.Valid()
    ensures it.Index() == |old(Model())| - 1 == |Model()| - 1 //no es capaz de deducirlo si no lo ponemos
    ensures it.Parent() == this
    ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
      it.Valid() && it.Parent() == old(it.Parent()) && it.Index() == old(it.Index())
  {
    it := new ArrayListIteratorImpl(this, size - 1);
    iterators := iterators + { it };
  }

  // Deletion of mid, next points to the next element (or past-the-end)
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
  {
    var midImpl := mid as ArrayListIteratorImpl;
   
    if (size == elements.Length) {
      Grow(elements.Length * 2 + 1, x);
    }
    assert size < elements.Length;
    assert Model() == old(Model());
    ShiftRight(midImpl.index);
    elements[midImpl.index] := x;
    size := size + 1;
    calc == {
      Model();
      old(Model()[..midImpl.index]) + [x] + old(Model()[midImpl.index..]);
      Seq.Insert(x, old(Model()), old(mid.Index()));
    }

    newt := midImpl.Copy();
    iterators := iterators + { newt };
  }

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

  method Grow(newCapacity: nat, elem: A)
    requires newCapacity >= elements.Length
    requires Valid()
    
    ensures Valid()
    ensures Model() == old(Model())
    ensures this.elements.Length == newCapacity

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr() - old(Repr()))
    
    ensures Iterators() == old(Iterators())
    modifies this
  {
    var newElements := new A[newCapacity] (_ => elem);
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

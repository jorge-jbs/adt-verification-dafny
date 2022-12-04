include "../../../src/linear/layer1/Stack.dfy"
include "../../../src/Utils.dfy"

class ArrayStackImpl<A> extends Stack<A> {
  var list: array<A>;
  var size: nat;

  function Repr0(): set<object>
    reads this
  {
    {list}
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
    && 0 <= size <= list.Length
  }

  function Model(): seq<A>
    reads this, list
    requires Valid()
    ensures Model() == Seq.Rev(list[0..size])
    ensures |Model()| == size
  {
    Seq.Rev(list[0..size])
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures forall x | x in Repr() :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    ReprDepth := 1;
    list := new A[0];
    size := 0;
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
  {
    s := size;
  }


  // O(1)
  method Top() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[0]
  { 
    assert Model() == Seq.Rev(list[0..size]);
    Seq.LastRev(list[0..size]);
    assert list[size - 1] == Seq.Rev(list[0..size])[0];
    x := list[size - 1];
  }

  method Grow(x: A)//auxiliary method to duplicate space
    modifies this, Repr()
    requires Valid()
    ensures Valid()
    ensures size == old(size)
    ensures list[0..size] == old(list[0..size])
    ensures Model() == old(Model())
    ensures list.Length > old(list.Length)
    ensures fresh(list)
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
  {
    //allocate new memory
    ghost var oldList := list[0..size];
    var aux: array<A> := new A[2 * list.Length + 1] (_ => x);
    var i := 0;
    while i < size
      decreases size-i
      invariant 0 <= i <= size <= list.Length < aux.Length && size==old(size)
      invariant aux[0..i] == list[0..i]
      invariant list[0..size] == old(list[0..size])
    {
      aux[i] := list[i];
      i := i + 1;
    }
    assert aux[0..size] == list[0..size] == old(list[0..size]);
    assert Seq.Rev(aux[0..size]) == Seq.Rev(list[0..size]) == Seq.Rev(old(list[0..size]));
    list := aux;
    assert Model() == Seq.Rev(aux[0..size]);
  }

  // O(1) amortized
  method Push(x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
  {
    if size == list.Length {
      Grow(x);
    }
    list[size] := x;
    size := size + 1;
    assert size == old(size) + 1;
    assert list[0..size] == old(list[0..size]) + [x];
    Seq.LastRev(list[0..size]);
    assert list[size - 1] == x;
  }

  // O(1)
  method Pop() returns (x: A)
    modifies this, Repr()
    requires allocated(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures allocated(Repr())

    requires Valid()
    requires !Empty?()
    ensures Valid()
    ensures [x] + Model() == old(Model())
  {
    x := list[size - 1];
    size := size - 1;
    assert list[0..size] + [x] == old(list[0..size]);
    assert size == old(size) - 1;
    assert |Model()| == |old(Model())| - 1;
    Seq.LastRev(list[0..old(size)]);
  }
}

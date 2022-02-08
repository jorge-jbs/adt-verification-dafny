include "../../../src/linear/layer1/Stack.dfy"
include "../../../src/Utils.dfy"

class ArrayStackImpl extends Stack {
  var list: array<int>;
  var size:nat;

  function ReprDepth(): nat
  {
    0
  }

  function Repr0(): set<object>
    reads this
  {
    {this, list}
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

  lemma UselessLemma()
    ensures Repr() == ReprFamily(1);
  {}

  predicate Valid()
    reads this, Repr()
  {
    0 <= size <= list.Length
  }

  function Model(): seq<int>
    reads this, list
    requires Valid()
    ensures Model()==Seq.Rev(list[0..size])
    ensures |Model()|==size
  {
    Seq.Rev(list[0..size])
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures forall x | x in Repr() :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    list := new int[10];
    size := 0;
  }

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []
  {
    size == 0
  }

  // O(1)
  function method Top(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Top() == Model()[0]
  { assert Model()==Seq.Rev(list[0..size]);
    Seq.LastRev(list[0..size]);
    assert list[size-1]==Seq.Rev(list[0..size])[0];
    list[size-1]
  }

  method grow()//auxiliary method to duplicate space
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures size==old(size)
    ensures list[0..size]==old(list[0..size])
    ensures Model()==old(Model())
    ensures list.Length>old(list.Length)
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
  {
    //allocate new memory
    ghost var oldList := list[0..size];
    var aux: array<int> := new int[2*list.Length+1];
    var i := 0;
    while i < size
      decreases size-i
      invariant 0 <= i <= size <= list.Length<aux.Length && size==old(size)
      invariant aux[0..i] == list[0..i]
      invariant list[0..size] == old(list[0..size])
    {
      aux[i] := list[i];
      i := i+1;
    }
    assert aux[0..size]==list[0..size]==old(list[0..size]);
    assert Seq.Rev(aux[0..size])==Seq.Rev(list[0..size])==Seq.Rev(old(list[0..size]));
    list := aux;
    assert Model() == Seq.Rev(aux[0..size]);
  }

  // O(1) amortized
  method Push(x: int)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    if size == list.Length {
      grow();
    }
    list[size]:=x;
    size:=size+1;
    assert size==old(size)+1;
    assert list[0..size]==old(list[0..size])+[x];
    Seq.LastRev(list[0..size]);
    assert list[size-1]==x;
  }

  // O(1)
  method Pop() returns (x: int)
    modifies Repr()
    requires size>0
    requires Valid()
    ensures Valid()
    ensures [x] + Model() == old(Model())
     ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    x:=list[size-1];
    size:=size-1;
    assert list[0..size]+[x]==old(list[0..size]);
    assert size==old(size)-1;
    assert |Model()|==|old(Model())|-1;
    Seq.LastRev(list[0..old(size)]);
  }
}

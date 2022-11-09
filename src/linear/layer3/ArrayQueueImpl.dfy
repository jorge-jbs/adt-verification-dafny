include "../../../src/linear/layer1/Queue.dfy"

class ArrayQueueImpl extends Queue<int> {
  var list: array<int>;
  var c: nat;
  var nelems: nat;

  function ReprDepth(): nat
    ensures ReprDepth() > 0
  {
    1
  }

  function Repr0(): set<object>
    reads this
  {
    {this, list}
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

  lemma UselessLemma()
    ensures Repr() == ReprFamily(ReprDepth());
  {}

  predicate Valid()
    reads this, Repr()
  {
    0 <= c < list.Length && 0 <= nelems <= list.Length
  }

  function Model(): seq<int> // Los elementos estan en [c..(c+nelems)%Length) circularmente
    reads this, Repr()
    requires Valid()
  {
    ModelAux(list,c,nelems)
  }

  function ModelAux(a:array<int>,c:nat,nelems:nat):seq<int>
    reads a
    requires 0 <= c < a.Length && 0 <= nelems <= a.Length
    ensures |ModelAux(a,c,nelems)|==nelems

  {

    if nelems == 0 then
      []
    else if c + nelems <= a.Length then
      a[c..c+nelems]
    else
      a[c..a.Length] + a[0..(c+nelems)%a.Length]
  }


  lemma incDeque(a:array<int>,c:nat,nelems:nat)
    requires 0<=c<a.Length &&0<nelems<=a.Length
    ensures ModelAux(a,c,nelems)==[a[c]]+ModelAux(a,(c+1)%a.Length,nelems-1)
  {
    if c + 1 < a.Length {
      assert ModelAux(a,c,nelems)==[a[c]]+ModelAux(a,(c+1),nelems-1);
      assert (c+1)%a.Length==c+1;
    }
  }

  lemma incEnque(a:array<int>,c:nat,nelems:nat)
    requires 0 <= c < a.Length && 0 <= nelems < a.Length
    ensures ModelAux(a, c, nelems+1) == ModelAux(a, c, nelems) + [a[(c+nelems)%a.Length]]
  {
    if c + nelems < a.Length { // consecutive nelems+1 elements [c..c+nelems]
      assert ModelAux(a, c, nelems+1)
        == ModelAux(a, c, nelems) + [a[(c+nelems)%a.Length]];
    } else { //elements [c..a.Length] followed by [0..(c+nelems+1)%a.Length]
      assert c+nelems+1 > a.Length && ((c+nelems+1)%a.Length)
        == (c+nelems) % a.Length+1;
      assert a[c..a.Length] + a[0..(c+nelems+1)%a.Length]
        == a[c..a.Length]+a[0..(c+nelems)%a.Length]+[a[(c+nelems)%a.Length]];
    }
  }

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []
  {
    nelems == 0
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    list := new int[10];
    c:=0;
    nelems:=0;
  }

  function method Front(): int
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Front() == Model()[0]
  {
    list[c]
  }

  // Auxiliary method to duplicate space
  method grow()
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures nelems==old(nelems)
    ensures Model()==old(Model())
    ensures list.Length>old(list.Length)
    ensures c+nelems<list.Length
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(list)
  {
      ghost var oldList := ModelAux(list,c,nelems);
      var aux: array<int> := new int[2*list.Length+1];
      var i := 0;
      while i < nelems
        decreases nelems-i
        invariant 0 <= i <= nelems <= list.Length < aux.Length
        invariant nelems == old(nelems)
        invariant 0 <= c < list.Length == old(list.Length)
        invariant ModelAux(aux, 0, i) == ModelAux(list, c, i)
        invariant ModelAux(list, c, nelems) == oldList
      {
        aux[i] := list[(c+i)%list.Length];
        i := i+1;
        assert aux[i-1] == list[(c+i-1)%list.Length];
        incEnque(aux, 0, old(i));
        incEnque(list, c, i-1);
      }
      assert ModelAux(aux, 0, nelems) == ModelAux(list, c, nelems) == oldList;
      list := aux;
      c := 0;
  }

  method Enqueue(x: int)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    ghost var oldList := ModelAux(list,c,nelems);
    if nelems == list.Length {
      grow();
    }
    assert ModelAux(list, c, nelems) == oldList;
    list[(c+nelems)%list.Length] := x;
    //assert 0<=(c+nelems)<list.Length ==> (c+nelems)%list.Length==c+nelems;
    assert c+nelems<list.Length ==> list[c..c+nelems]==oldList;
    assert c+nelems>list.Length ==> list[c..list.Length]+list[0..(c+nelems)%list.Length]==oldList;
    nelems := nelems + 1;
    incEnque(list, c, nelems-1);
  }

  method Dequeue() returns (x: int)
    modifies Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    x := list[c];
    c := (c+1) % list.Length;
    nelems := nelems-1;
    incDeque(list, old(c), old(nelems));
    // assert ModelAux(list,old(c),f,old(nelems))==[list[old(c)]]+ModelAux(list,(old(c)+1)%list.Length,f,nelems);
  }
}

include "../../../src/linear/layer1/Deque.dfy"

class ArrayDequeImpl<A> extends Deque<A> {
  var list: array<A>;
  var c: nat;
  var nelems: nat;

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

  predicate Valid()
    reads this, Repr()
  {
    && ReprDepth == 1
    && (list.Length != 0 ==> 0 <= c < list.Length)
    && (list.Length == 0 ==> c == 0)
    && 0 <= nelems <= list.Length
  }

  function Model(): seq<A> // Los elementos estan en [c..(c+nelems)%Length) circularmente
    reads this, Repr()
    requires Valid()
  {
    ModelAux(list, c, nelems)
  }

  static function ModelAux(a: array<A>, c: nat, nelems: nat): seq<A>
    reads a
    requires a.Length != 0 ==> 0 <= c < a.Length
    requires 0 <= nelems <= a.Length
    requires a.Length == 0 ==> c == 0
    ensures |ModelAux(a, c, nelems)| == nelems
  {
    if c + nelems <= a.Length then
      a[c..c + nelems]
    else
      a[c..a.Length] + a[0..(c + nelems) % a.Length]
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    ReprDepth := 1;
    list := new A[0];
    c := 0;
    nelems := 0;
  }

  lemma IncDeque(a: array<A>, c: nat, nelems: nat)
    requires 0 <= c < a.Length && 0 < nelems <= a.Length
    ensures ModelAux(a, c, nelems) == [a[c]] + ModelAux(a, (c + 1) % a.Length, nelems - 1)
  {
    if c + 1 < a.Length {
      assert ModelAux(a, c, nelems) == [a[c]] + ModelAux(a, c + 1, nelems - 1);
      assert (c + 1) % a.Length == c + 1;
    }
  }

  static lemma IncEnque(a: array<A>, c: nat, nelems: nat)
    requires a.Length > 0
    requires 0 <= c < a.Length && 0 <= nelems < a.Length
    ensures ModelAux(a, c, nelems + 1) == ModelAux(a, c, nelems) + [a[(c + nelems) % a.Length]]
  {
    if c + nelems < a.Length { // consecutive nelems+1 elements [c..c+nelems]
      assert ModelAux(a, c, nelems+1)
        == ModelAux(a, c, nelems) + [a[(c + nelems) % a.Length]];
    } else { //elements [c..a.Length] followed by [0..(c+nelems+1)%a.Length]
      assert c + nelems + 1 > a.Length && ((c + nelems + 1) % a.Length)
        == (c+nelems) % a.Length + 1;
      assert a[c..a.Length] + a[0..(c + nelems + 1) % a.Length]
        == a[c..a.Length]+a[0..(c + nelems) % a.Length]+[a[(c + nelems) % a.Length]];
    }
  }

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []
  {
    nelems == 0
  }

  // Auxiliary method to duplicate space
  method Grow(x: A)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures nelems == old(nelems)
    ensures Model() == old(Model())
    ensures list.Length > old(list.Length)
    ensures c + nelems < list.Length
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(list)
  {
    ghost var oldList := ModelAux(list, c, nelems);
    var aux: array<A> := new A[2 * list.Length + 1] (_ => x);
    var i := 0;
    while i < nelems
      decreases nelems-i
      invariant 0 <= i <= nelems <= list.Length < aux.Length
      invariant nelems == old(nelems)
      invariant list.Length != 0 ==> 0 <= c < list.Length
      invariant list.Length == 0 ==> c == 0
      invariant list.Length == old(list.Length)
      invariant ModelAux(aux, 0, i) == ModelAux(list, c, i)
      invariant ModelAux(list, c, nelems) == oldList
    {
      aux[i] := list[(c + i) % list.Length];
      i := i+1;
      assert aux[i - 1] == list[(c + i - 1) % list.Length];
      IncEnque(aux, 0, i);
      IncEnque(list, c, i - 1);
    }
    assert ModelAux(aux, 0, nelems) == ModelAux(list, c, nelems) == oldList;
    list := aux;
    c := 0;
  }

  function method Back(): A
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Back() == Model()[|Model()| - 1]
  {
    assert list[(c + nelems - 1) % list.Length] == Model()[|Model()| - 1];
    list[(c + nelems - 1) % list.Length]
  }

  method PushBack(x: A)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    ghost var oldList := ModelAux(list,c,nelems);
    if nelems == list.Length {
      Grow(x);
    }

    assert ModelAux(list, c, nelems) == oldList;

    list[(c + nelems) % list.Length] := x;

    Modulo(c + nelems, list.Length);
    assert c + nelems < list.Length ==> (c + nelems) % list.Length == c + nelems;
    assert c + nelems < list.Length ==> list[c..c + nelems] == oldList;
    assert c + nelems > list.Length ==> list[c..list.Length] + list[0..(c + nelems) % list.Length] == oldList;

    nelems := nelems + 1;

    IncEnque(list, c, nelems - 1);
  }

  lemma Modulo(a:int,b:int)
    requires b != 0
    ensures 0 <= a < b ==> a / b == 0 && a % b == a
  {}

  method PopBack() returns (x: A)
    modifies Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Model() + [x] == old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    x := list[(c + nelems - 1) % list.Length];
    nelems := nelems - 1;
    //assert c+nelems==0 ==> (c+nelems-1)%list.Length==list.Length-1;
  }

  function method Front(): A
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Front() == Model()[0]
  {
    list[c]
  }

  method PushFront(x: A)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures forall x | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
  {
    ghost var oldList := ModelAux(list,c,nelems);
    if nelems == list.Length {
      Grow(x);
    }
    assert ModelAux(list, c, nelems) == oldList;
    if (c == 0) {
      c := list.Length-1;
    } else {
      c := c - 1;
    }
    list[c] := x;
    nelems := nelems + 1;
    assert Model() == [x] + old(Model());
    //IncEnque(list, c, nelems-1);
  }

  method PopFront() returns (x: A)
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
    nelems := nelems - 1;
    IncDeque(list, old(c), old(nelems));
    // assert ModelAux(list,old(c),f,old(nelems))==[list[old(c)]]+ModelAux(list,(old(c)+1)%list.Length,f,nelems);
  }
}

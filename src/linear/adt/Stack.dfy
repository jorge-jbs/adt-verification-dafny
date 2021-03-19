include "../../../src/linear/implementation/SinglyLinkedListWithSpine.dfy"
include "../../../src/linear/interface/Stack.dfy"

class Stack1 extends Stack {
  var list: List<int>;

  function Depth(): nat
  {
    1
  }

  function Repr0(): set<object>
    reads this
  {
    {list}
  }

  function Repr1(): set<object>
    reads this, Repr0()
  {
    {list} + list.Repr()
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
    else
      ReprFamily(n-1)
  }

  lemma UselessLemma()
    ensures Repr() == ReprFamily(1);
  {}

  predicate Valid()
    reads this, Repr()
  {
    list.Valid()
  }

  function Model(): seq<int>
    reads this, list, list.spine
    requires Valid()
  {
    list.Model()
  }

  constructor()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    list := new List();
  }

  function method Empty(): bool
    reads this, Repr()
    requires Valid()
    ensures Empty() <==> Model() == []
  {
    list.head == null
  }

  // O(1)
  method Top() returns (x: int)
    requires Valid()
    requires Model() != []
    ensures x == Model()[0]
  {
    x := list.head.data;
  }

  // O(1)
  method Push(x: int)
    modifies list
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures list == old(list)
  {
    list.Push(x);
  }

  // O(1)
  method Pop() returns (x: int)
    modifies list
    requires list.head != null
    requires Valid()
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
  {
    x := list.Pop();
  }

  // method Reverse()
  //   modifies this, Repr()
  //   requires Valid()
  //   ensures Valid()
  //   ensures Model() == Seq.Rev(old(Model()))
  //   ensures Repr() == old(Repr())
}

function method abs(x: int): int
{
  if x < 0 then
    -x
  else
    x
}

// lemma lemma1(v: array<int>, i: int)
//   requires forall i | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i+1])
//   requires 0 <= i <= v.Length
//   ensures forall j | 0 <= j < i :: abs(v[j]) <= abs(v[i])

method Reverse(st: Stack)
  modifies st, st.Repr()
  requires st.Valid()
  ensures st.Valid()
  ensures st.Model() == Seq.Rev(old(st.Model()))
  ensures forall x | x in st.Repr() - old(st.Repr()) :: fresh(x)

method split(v: array<int>, neg: Stack, pos: Stack)
  modifies pos, pos.Repr(), neg, neg.Repr()
  requires neg.Valid()
  requires neg.Empty()
  requires pos.Valid()
  requires pos.Empty()
  requires pos.Repr() !! neg.Repr()

  ensures pos.Valid()
  ensures neg.Valid()
  ensures pos.Repr() !! neg.Repr()

  ensures forall x | x in neg.Repr() - old(neg.Repr()) :: fresh(x)
  ensures forall x | x in neg.Model() :: x < 0
  ensures forall i | 0 <= i < |neg.Model()| - 1 :: abs(neg.Model()[i]) >= abs(neg.Model()[i+1])

  ensures forall x | x in pos.Repr() - old(pos.Repr()) :: fresh(x)
  ensures forall x | x in pos.Model() :: x >= 0
  ensures forall i | 0 <= i < |pos.Model()| - 1 :: abs(pos.Model()[i]) >= abs(pos.Model()[i+1])

  ensures Seq.MElems(neg.Model()) + Seq.MElems(pos.Model()) == Seq.MElems(v[..])
/*
{
  var i := 0;
  while i < v.Length
    invariant i <= v.Length

    invariant forall i | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i+1])

    invariant neg.Repr() !! pos.Repr()
    invariant forall x | x in neg.Repr() :: fresh(x)
    invariant forall x | x in pos.Repr() :: fresh(x)
    // invariant neg != pos

    invariant forall x | x in neg.Repr() :: fresh(x)
    invariant neg.Valid()
    invariant forall x | x in neg.Model() :: x < 0
    invariant forall i | 0 <= i < |neg.Model()| - 1 :: abs(neg.Model()[i]) >= abs(neg.Model()[i+1])
    // invariant forall i | 0 <= i < |neg.Model()| - 1 :: neg.Model()[i] <= neg.Model()[i+1]

    invariant forall x | x in pos.Repr() :: fresh(x)
    invariant pos.Valid()
    invariant forall x | x in pos.Model() :: x >= 0
    invariant forall i | 0 <= i < |pos.Model()| - 1 :: abs(pos.Model()[i]) >= abs(pos.Model()[i+1])
    // invariant forall i | 0 <= i < |neg.Model()| - 1 :: neg.Model()[i] >= neg.Model()[i+1]

    invariant Seq.MElems(neg.Model()) + Seq.MElems(pos.Model())
      == Seq.MElems(v[..i])

  {
    lemma1(v, i);
    assert forall j | 0 <= j < i :: abs(v[j]) <= abs(v[i]);
    if v[i] < 0 {
      assert Seq.MElems(neg.Model()) + Seq.MElems(pos.Model())
        == Seq.MElems(v[..i]);
      assert Seq.MElems(neg.Model())
        == Seq.MElems(v[..i]) - Seq.MElems(pos.Model());
      assert forall x | x in Seq.MElems(neg.Model()) :: x in Seq.MElems(v[..i]) - Seq.MElems(pos.Model());
      assert forall x | x in Seq.MElems(neg.Model()) :: x in Seq.MElems(v[..i]);
      // assert forall x | x in Seq.MElems(neg.Model()) :: x in neg.Model();
      assert forall x | x in neg.Model() :: x in Seq.MElems(neg.Model());
      assert forall x | x in neg.Model() :: x in v[..i];
      assert forall x | x in neg.Model() :: exists j | 0 <= j < i :: v[j] == x;
      assert forall x | x in neg.Model() :: abs(v[i]) >= x;
      assert |neg.Model()| > 0 ==> neg.Model()[0] in neg.Model();
      assert |neg.Model()| > 0 ==> abs(v[i]) >= neg.Model()[0];
      // assert forall j | 0 <= j < |neg.Model()| :: neg.Model()[j] in v[..i];
      // assert forall j | 0 <= j < |neg.Model()| :: abs(neg.Model()[j]) <= abs(v[i]);
      // assert forall j | 0 <= j < |neg.Model()| :: neg.Model()[j] <= v[i];
      neg.Push(v[i]);
    } else {
      assert Seq.MElems(pos.Model()) + Seq.MElems(neg.Model())
        == Seq.MElems(v[..i]);
      assert Seq.MElems(pos.Model())
        == Seq.MElems(v[..i]) - Seq.MElems(neg.Model());
      assert forall x | x in Seq.MElems(pos.Model()) :: x in Seq.MElems(v[..i]) - Seq.MElems(neg.Model());
      assert forall x | x in Seq.MElems(pos.Model()) :: x in Seq.MElems(v[..i]);
      // assert forall x | x in Seq.MElems(pos.Model()) :: x in pos.Model();
      assert forall x | x in pos.Model() :: x in Seq.MElems(pos.Model());
      assert forall x | x in pos.Model() :: x in v[..i];
      assert forall x | x in pos.Model() :: exists j | 0 <= j < i :: v[j] == x;
      assert forall x | x in pos.Model() :: abs(v[i]) >= x;
      assert |pos.Model()| > 0 ==> pos.Model()[0] in pos.Model();
      assert |pos.Model()| > 0 ==> abs(v[i]) >= pos.Model()[0];
      assert forall x | x in pos.Model() :: exists j | 0 <= j < i :: v[j] == x;
      assert forall x | x in pos.Model() :: abs(v[i]) >= x;
      assert |pos.Model()| > 0 ==> pos.Model()[0] in pos.Model();
      assert |pos.Model()| > 0 ==> abs(v[i]) >= pos.Model()[0];
      pos.Push(v[i]);
    }
    i := i + 1;
  }
}
*/

method FillFromStack(r: array<int>, i: nat, st: Stack) returns (l: nat)
  modifies st, st.Repr()
  requires st.Valid()
  requires i + |st.Model()| <= r.Length
  ensures st.Valid()
  ensures st.Empty()
  ensures forall x | x in st.Repr() - old(st.Repr()) :: fresh(x)
  ensures r[i..i+old(|st.Model()|)] == old(st.Model())
  ensures Seq.MElems(r[i..i+old(|st.Model()|)]) == Seq.MElems(old(st.Model()))
  ensures l == i + old(|st.Model()|)

method reordenandoLaCola(v: array<int>) returns (r: array<int>)
  requires forall i | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i+1])
  ensures v.Length == r.Length
  ensures Array.melems(v) == Array.melems(r)
  ensures forall i | 0 <= i < r.Length - 1 :: r[i] <= r[i+1]
{
  var neg: Stack := new Stack1();
  var pos: Stack := new Stack1();
  split(v, neg, pos);
  assert Seq.MElems(neg.Model()) + Seq.MElems(pos.Model()) == Seq.MElems(v[..]);
  calc == {
    |neg.Model()| + |pos.Model()|;
    |Seq.MElems(neg.Model())| + |Seq.MElems(pos.Model())|;
    |Seq.MElems(neg.Model()) + Seq.MElems(pos.Model())|;
    |Seq.MElems(v[..])|;
    |v[..]|;
    v.Length;
  }
  assert |neg.Model()| + |pos.Model()| == |v[..]| == v.Length;
  var i := 0;
  r := new int[v.Length];
  ghost var onegmodel := neg.Model();
  ghost var oposmodel := pos.Model();
  assert |onegmodel| + |oposmodel| == v.Length;
  assert neg.Repr() !! pos.Repr();
  assert pos !in neg.Repr();
  assert pos != neg;
  i := FillFromStack(r, i, neg);
  assert |onegmodel| + |oposmodel| == v.Length;
  assert i == |onegmodel|;
  assert pos.Valid();
  Reverse(pos);
  assert pos.Model() == Seq.Rev(oposmodel);
  assert |pos.Model()| == |oposmodel|;
  assert i + |pos.Model()| == i + |oposmodel| == |onegmodel| + |oposmodel| == v.Length == r.Length;
  i := FillFromStack(r, i, pos);
  /*
  while !neg.Empty()
    decreases neg.Model()

    invariant 0 <= i <= r.Length

    invariant neg.Valid()
    invariant pos.Valid()
    invariant forall x | x in neg.Repr() :: fresh(x)
    invariant forall x | x in pos.Repr() :: fresh(x)

    invariant r[..i] + neg.Model() == onegmodel
    invariant forall j | 0 <= j < i-1 :: r[j] <= r[j+1]
  {
    var x := neg.Pop();
    r[i] := x;
    i := i + 1;
  }

  Reverse(pos);
  // pos.Reverse();
  ghost var oposmodel := pos.Model();
  assert r[..i] == onegmodel;
  assert pos.Model() == oposmodel;
  while !pos.Empty()
    decreases pos.Model()

    invariant 0 <= i <= r.Length

    invariant neg.Valid()
    invariant pos.Valid()
    invariant forall x | x in neg.Repr() :: fresh(x)
    invariant forall x | x in pos.Repr() :: fresh(x)

    invariant r[..i] + pos.Model() == onegmodel + oposmodel
    invariant forall j | 0 <= j < i-1 :: r[j] <= r[j+1]
  {
    var x := pos.Pop();
    r[i] := x;
    i := i + 1;
  }
  assert i == r.Length;
     */
}

/*
method EvalPostfix(s: string) returns (res: int)
  requires forall c | c in s :: c in "0123456789+-*//*"
{
  var st: Stack := new Stack1();
  var i := 0;
  while i < |s|
    invariant forall x | x in st.Repr() :: fresh(x)
    invariant st.Valid()
  {
    var c := s[0];
    if c in "0123456789" {
      st.Push((c as int) - 48);
    } else {
      if st.Empty() {
        return -1;
      }
      var x := st.Pop();
      if st.Empty() {
        return -1;
      }
      var y := st.Pop();
      var n: int;
      if c == '+' {
        n := x + y;
      } else if c == '-' {
        n := x - y;
      } else if c == '*' {
        n := x * y;
      } else if c == '/' {
        if y == 0 {
          return -1;
        }
        assert y != 0;
        n := x / y;
      }
      st.Push(n);
    }
    i := i + 1;
  }
  if st.Empty() {
    return -1;
  }
  assert !st.Empty();
  res := st.Top();
}

function method OpeningBrace(c: char): (d: char)
  requires c == ')' || c == ']' || c == '}'
{
  if c == ')' then
    '('
  else if c == ']' then
    '['
  else
    '{'
}

method BalancedTest(s: string) returns (b: bool)
{
  var st: Stack := new Stack1();
  var i := 0;
  while i < |s|
    invariant forall x | x in st.Repr() :: fresh(x)
    invariant st.Valid()
  {
    if s[i] == '('  || s[i] == '[' || s[i] == '{' {
        st.Push(s[i] as int);
    } else if s[i] == ')' || s[i] == ']' || s[i] == '}' {
      if st.Empty() {
        return false;
      } else {
        var c := st.Pop();
        if c != OpeningBrace(s[i]) as int {
          return false;
        }
      }
    }
    i := i + 1;
  }
  return st.Empty();
}

method Print(st: Stack)
  modifies st, st.Repr()
  requires st.Valid()
  ensures st.Valid()
  ensures st.Empty()
{
  while !st.Empty()
    decreases |st.Model()|
    invariant st.Valid()
    invariant forall x | x in st.Repr() - old(st.Repr()) :: fresh(x)
  {
    var x := st.Pop();
    print x;
    print "\n";
  }
}

method Main() {
  var st: Stack := new Stack1();
  st.Push(3);
  st.Push(2);
  st.Push(1);
  Print(st);
}
*/

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
    ensures forall x | x in Repr() :: fresh(x)
    ensures forall x | x in Repr() :: allocated(x)
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

// method Main() {
//   var st: Stack := new Stack1();
//   st.Push(3);
//   st.Push(2);
//   st.Push(1);
//   Print(st);
// }

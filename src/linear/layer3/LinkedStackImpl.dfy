include "../../../src/linear/layer1/Stack.dfy"
include "../../../src/linear/layer4/SinglyLinkedListWithSpine.dfy"

class LinkedStack<A> extends Stack<A> {
  var list: List<A>;

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

  predicate Valid()
    reads this, Repr()
  {
    && ReprDepth == 1
    && list.Valid()
  }

  function Model(): seq<A>
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
    ReprDepth := 1;
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
  function method Top(): A
    reads this, Repr()
    requires Valid()
    requires Model() != []
    ensures Top() == Model()[0]
  {
    list.head.data
  }

  // O(1)
  method Push(x: A)
    modifies Repr()
    requires Valid()
    ensures Valid()
    ensures Model() == [x] + old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    list.Push(x);
  }

  // O(1)
  method Pop() returns (x: A)
    modifies Repr()
    requires forall x | x in Repr()::allocated(x)
    requires Valid()
    requires !Empty()
    ensures Valid()
    ensures [x] + Model() == old(Model())

    ensures forall x {:trigger x in Repr(), x in old(Repr())} | x in Repr() - old(Repr()) :: fresh(x)
    ensures fresh(Repr()-old(Repr()))
    ensures forall x | x in Repr() :: allocated(x)
  {
    x := list.Pop();
  }
}

method EvalPostfix(s: string) returns (res: int)
  requires forall c | c in s :: c in "0123456789+-*//*"
{
  var st: Stack := new LinkedStack();
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
  var st: Stack := new LinkedStack();
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
  requires forall x | x in st.Repr() :: allocated(x)
  requires st.Valid()
  ensures st.Valid()
  ensures st.Empty()
  requires forall x | x in st.Repr() :: allocated(x)
  ensures forall x {:trigger x in st.Repr(), x in old(st.Repr())} | x in st.Repr() - old(st.Repr()) :: fresh(x)
  ensures fresh(st.Repr()-old(st.Repr()))
  ensures forall x | x in st.Repr() :: allocated(x)
{
  while !st.Empty()
    decreases |st.Model()|
    invariant st.Valid()
    invariant forall x {:trigger x in st.Repr(), x in old(st.Repr())} | x in st.Repr() - old(st.Repr()) :: fresh(x)
    invariant fresh(st.Repr()-old(st.Repr()))
    invariant forall x | x in st.Repr() :: allocated(x)
  {
    var x := st.Pop();
    print x;
    print "\n";
  }
}

method PopTwice(s: Stack)
  modifies s, s.Repr()
  requires s.Valid() && |s.Model()| >= 2
  requires forall x | x in s.Repr() :: allocated(x)
  ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
  ensures fresh(s.Repr()-old(s.Repr()))
  ensures forall x | x in s.Repr() :: allocated(x)
{
  var x := s.Pop();
  x := s.Pop();
}

method PopToArray(s: Stack<int>, init: nat, n: nat, v: array<int>)
  modifies v, s, s.Repr()
  requires s.Valid()
  requires n <= |s.Model()|
  requires init <= n
  requires n <= v.Length - init

  requires {v} !! {s} + s.Repr()
  requires forall x | x in s.Repr() :: allocated(x)

  ensures s.Valid()
  ensures old(s.Model()[..n]) == v[init..init+n]
  ensures old(s.Model()[n..]) == s.Model()

  ensures {v} !! {s} + s.Repr()
  requires forall x | x in s.Repr() :: allocated(x)
  ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
  ensures fresh(s.Repr()-old(s.Repr()))
  ensures forall x | x in s.Repr() :: allocated(x)
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s.Valid()
    invariant s.Model() == old(s.Model()[i..])
    invariant v[init..init+i] == old(s.Model()[..i])

    invariant forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
    invariant fresh(s.Repr()-old(s.Repr()))
    invariant forall x | x in s.Repr() :: allocated(x)
  {
    v[init+i] := s.Pop();
    i := i + 1;
  }
}

method PushFromArray(s: Stack<int>, a: array<int>)
  modifies s, s.Repr()
  requires s.Valid()
  requires {a} !! {s} + s.Repr()

  requires forall x | x in s.Repr() :: allocated(x)

  ensures s.Valid()
  ensures s.Model() == Seq.Rev(a[..]) + old(s.Model())

  requires forall x | x in s.Repr() :: allocated(x)
  ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
  ensures fresh(s.Repr()-old(s.Repr()))
  ensures forall x | x in s.Repr() :: allocated(x)
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant s.Valid()
    invariant s.Model() == Seq.Rev(a[..i]) + old(s.Model())

    invariant forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
    invariant fresh(s.Repr()-old(s.Repr()))
    invariant forall x | x in s.Repr() :: allocated(x)
  {
    s.Push(a[i]);

    { // GHOST
      Seq.LastRev(a[..i+1]);
      assert |a[..i]| == i;
      assert |a[..i+1]|-1 == i;
      assert a[..i+1][..i] == a[..i];
      assert Seq.Rev(a[..i+1]) == [a[i]] + Seq.Rev(a[..i]);
    }

    i := i + 1;
  }
  assert a[..a.Length] == a[..];
}

method DoNothingNTimes(s: Stack, n: nat)
  modifies s, s.Repr()
  requires s.Valid()
  requires !s.Empty()

  requires forall x | x in s.Repr() :: allocated(x)

  ensures s.Valid()
  ensures s.Model() == old(s.Model())

  requires forall x | x in s.Repr() :: allocated(x)
  ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
  ensures fresh(s.Repr()-old(s.Repr()))
  ensures forall x | x in s.Repr() :: allocated(x)
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s.Valid()
    invariant s.Model() == old(s.Model())

    invariant forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
    invariant fresh(s.Repr()-old(s.Repr()))
    invariant forall x | x in s.Repr() :: allocated(x)
  {
    var x := s.Pop();
    s.Push(x);
    i := i + 1;
  }
}

method Clear(s: Stack)
  modifies s, s.Repr()
  requires s.Valid()
  ensures s.Valid()
  ensures s.Empty()

  requires forall x | x in s.Repr() :: allocated(x)
  ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
  ensures fresh(s.Repr()-old(s.Repr()))
  ensures forall x | x in s.Repr() :: allocated(x)
{
  while !s.Empty()
    decreases |s.Model()|
    invariant s.Valid()
    invariant forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
    invariant fresh(s.Repr()-old(s.Repr()))
    invariant forall x | x in s.Repr() :: allocated(x)
  {
    var x := s.Pop();
  }
}

method FromStackToArray(s: Stack<int>, a: array<int>, n: nat)
  modifies a, s, s.Repr()
  requires s.Valid()
  requires {a} !! {s} + s.Repr()
  requires a.Length - n >= |s.Model()|
  ensures s.Valid()
  ensures s.Empty()
  ensures a[..n] == old(a[..n])
  ensures a[n..n+old(|s.Model()|)] == old(s.Model())
  ensures a[n+old(|s.Model()|)..] == old(a[n+|s.Model()|..])

  requires forall x | x in s.Repr() :: allocated(x)
  ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
  ensures fresh(s.Repr()-old(s.Repr()))
  ensures forall x | x in s.Repr() :: allocated(x)
{
  var i := 0;
  while !s.Empty()
    decreases |s.Model()|
    invariant 0 <= i <= old(|s.Model()|)
    invariant s.Valid()
    invariant i + |s.Model()| == old(|s.Model()|)
    invariant a[..n] == old(a[..n])
    invariant a[n..n+i] + s.Model() == old(s.Model())
    invariant a[n+i..] == old(a[n+i..])
    invariant forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
    invariant fresh(s.Repr()-old(s.Repr()))
    invariant forall x | x in s.Repr() :: allocated(x)
  {
    a[n+i] := s.Pop();
    i := i + 1;
  }
  assert i == old(|s.Model()|);
}

method {:timeLimitMultiplier 4} PopPush(s: Stack, t: Stack)
  modifies s, s.Repr(), t, t.Repr()
  requires s.Valid() && !s.Empty()
  requires t.Valid()
  requires {s} + s.Repr() !! {t} + t.Repr()

  ensures s.Valid() && t.Valid()
  ensures {s} + s.Repr() !! {t} + t.Repr()
  ensures [old(s.Model()[0])] + s.Model() == old(s.Model())
  ensures t.Model() == [old(s.Model()[0])] + old(t.Model())
  ensures Seq.Rev(old(s.Model())) + old(t.Model())
    == Seq.Rev(s.Model()) + t.Model()

  requires forall x | x in s.Repr() :: allocated(x)
  ensures forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
  ensures fresh(s.Repr()-old(s.Repr()))
  ensures forall x | x in s.Repr() :: allocated(x)

  requires forall x | x in t.Repr() :: allocated(x)
  ensures forall x {:trigger x in t.Repr(), x in old(t.Repr())} | x in t.Repr() - old(t.Repr()) :: fresh(x)
  ensures fresh(t.Repr()-old(t.Repr()))
  ensures forall x | x in t.Repr() :: allocated(x)
{
  var x := s.Pop();
  t.Push(x);
}

method {:timeLimitMultiplier 2} Extract(s: Stack, t: Stack)
  modifies s, s.Repr(), t, t.Repr()
  requires s.Valid() && !s.Empty()
  requires t.Valid()
  requires {s} + s.Repr() !! {t} + t.Repr()
  requires forall y | y in s.Repr() :: allocated(y)
  requires forall y | y in t.Repr() :: allocated(y)
  ensures s.Valid() && t.Valid()
  ensures {s} + s.Repr() !! {t} + t.Repr()
  ensures s.Model() == []
  ensures t.Model() == Seq.Rev(old(s.Model())) + old(t.Model())

  ensures forall x | x in s.Repr() - old(s.Repr()) :: fresh(x)
  ensures forall x | x in t.Repr() - old(t.Repr()) :: fresh(x)
  ensures forall x | x in s.Repr() :: allocated(x)
  ensures forall x | x in t.Repr() :: allocated(x)
{
  ghost var i := 0;
  while !s.Empty()
    decreases |s.Model()|
    invariant s.Valid() && t.Valid()
    invariant {s} + s.Repr() !! {t} + t.Repr()
    invariant 0 <= i <= old(|s.Model()|)
    invariant i == old(|s.Model()|) - |s.Model()|
    invariant Seq.Rev(old(s.Model())) + old(t.Model())
      == Seq.Rev(s.Model()) + t.Model()

    invariant forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
    invariant fresh(s.Repr()-old(s.Repr()))
    invariant forall x | x in s.Repr() :: allocated(x)
    invariant forall x {:trigger x in t.Repr(), x in old(t.Repr())} | x in t.Repr() - old(t.Repr()) :: fresh(x)
    invariant fresh(t.Repr()-old(t.Repr()))
    invariant forall x | x in t.Repr() :: allocated(x)
  {
    PopPush(s, t);
    /*
    var x := s.Pop();
    assert x == old(s.Model()[i]);
    t.Push(x);
    Seq.LastRev(old(s.Model()[..i+1]));
    assert old(|s.Model()[..i+1]|) == i+1;
    assert old(s.Model()[..i+1][..i]) == old(s.Model()[..i]);

    calc == {
      t.Model();
      [old(s.Model()[i])] + Seq.Rev(old(s.Model()[..i])) + old(t.Model());
      Seq.Rev(old(s.Model()[..i+1])) + old(t.Model());
    }
    */
    i := i+1;
  }
  assert i == old(|s.Model()|);
  assert old(s.Model()[..i]) == old(s.Model());
}

/*
method {:verify false} miniPrueba(s:Stack, q:Queue)
modifies s.Repr(), q.Repr()
requires s.Valid() && q.Valid() &&!s.Empty()
requires ({s}+s.Repr()) !! ({q}+q.Repr())
requires forall y | y in s.Repr()::allocated(y)
requires forall y | y in q.Repr()::allocated(y)
ensures s.Valid() && q.Valid()
ensures forall x | x in q.Repr()-old(q.Repr()) :: fresh(x)
ensures forall x | x in s.Repr()-old(s.Repr()) :: fresh(x)
ensures forall y | y in s.Repr()::allocated(y)//Esto no se si hara falta cuando la llamemos
ensures forall y | y in q.Repr()::allocated(y)
ensures [old(s.Model()[0])]+s.Model()==old(s.Model())
ensures q.Model()==old(q.Model())+[old(s.Model()[0])]
{

  var y:=s.Pop();
  q.Enqueue(y);

}

method {:verify false} miniPrueba2(s:LinkedStack, q:Queue2)
modifies s.Repr(), q.Repr()
requires s.Valid() && q.Valid() &&!s.Empty()
requires ({s}+s.Repr()) !! ({q}+q.Repr())
 ensures s.Valid() && q.Valid()
ensures forall x | x in q.Repr()-old(q.Repr()) :: fresh(x)
ensures [old(s.Model()[0])]+s.Model()==old(s.Model())
ensures q.Model()==old(q.Model())+[old(s.Model()[0])]
{
  var y:=s.Pop();
  q.Enqueue(y);
}

//Precondicion: validas+disjuntas+allocated
//Postcondicion: validas+disjuntas+frescas+allocated

method {:verify false}{:timeLimitMultiplier 4} letsprintTheStacktoQueue(s:Stack, q:Queue)
modifies s.Repr(), q.Repr()
requires s.Valid() && q.Valid()
requires ({s}+s.Repr()) !! ({q}+q.Repr())
requires forall y | y in s.Repr()::allocated(y)
requires forall y | y in q.Repr()::allocated(y)
ensures ({s}+s.Repr()) !! ({q}+q.Repr())
ensures forall x | x in q.Repr()-old(q.Repr()) :: fresh(x)
ensures forall x | x in s.Repr()-old(s.Repr()) :: fresh(x)
ensures forall y | y in s.Repr()::allocated(y)//estas no se si son necesarias
ensures forall y | y in q.Repr()::allocated(y)
ensures s.Valid() && q.Valid()
ensures s.Empty()
ensures q.Model() == old(q.Model())+old(s.Model())
{
 while (!s.Empty())
   decreases |s.Model()|
   invariant (s.Repr()-old(s.Repr())) !! (q.Repr()-old(q.Repr()))
   invariant forall y | y in s.Repr()::allocated(y)
  invariant forall y | y in q.Repr()::allocated(y)
   invariant forall x | x in (q.Repr()-old(q.Repr()))+(s.Repr()-old(s.Repr())) :: fresh(x)
   invariant s.Valid() && q.Valid() && ({s}+s.Repr()) !! ({q}+q.Repr())
   invariant q.Model()+s.Model()==old(q.Model())+old(s.Model())
 {
  var y:=s.Pop();
  q.Enqueue(y);
 }
}
   */

function InitInCommon<A>(xs: seq<A>, ys: seq<A>): nat
  ensures InitInCommon(xs, ys) <= |xs|
  ensures InitInCommon(xs, ys) <= |ys|
  ensures forall i | 0 <= i < InitInCommon(xs, ys) :: xs[i] == ys[i]
  ensures xs[..InitInCommon(xs, ys)] == ys[..InitInCommon(xs, ys)]
  ensures InitInCommon(xs, ys) < |xs| && InitInCommon(xs, ys) < |ys|
    ==> xs[InitInCommon(xs, ys)] != ys[InitInCommon(xs, ys)]
{
  if xs != [] && ys != [] && xs[0] == ys[0] then
    1 + InitInCommon(xs[1..], ys[1..])
  else
    0
}

method {:timeLimitMultiplier 8} areEqual(s: Stack<int>, r: Stack<int>)
  returns (b: bool)
  modifies s, s.Repr(), r, r.Repr()
  requires s.Valid() && r.Valid()
  requires {s} + s.Repr() !! {r} + r.Repr()

  requires forall x | x in s.Repr() :: allocated(x)
  requires forall x | x in r.Repr() :: allocated(x)

  ensures s.Valid() && r.Valid()
  ensures {s} + s.Repr() !! {r} + r.Repr()
  ensures b <==> old(s.Model()) == old(r.Model())
  ensures b <==> s.Empty() && r.Empty()
  ensures s.Model() == old(s.Model()[InitInCommon(s.Model(), r.Model())..])
  ensures r.Model() == old(r.Model()[InitInCommon(s.Model(), r.Model())..])

  ensures forall x | x in r.Repr() - old(r.Repr()) :: fresh(x)
  ensures forall x | x in s.Repr() - old(s.Repr()) :: fresh(x)
  ensures forall x | x in s.Repr() :: allocated(x)
  ensures forall x | x in r.Repr() :: allocated(x)
{
  ghost var i: nat := 0;
  ghost var ls := |s.Model()|;
  ghost var lr := |r.Model()|;
  ghost var ms := s.Model();
  ghost var mr := r.Model();
  while !s.Empty() && !r.Empty() && s.Top() == r.Top()
    decreases |s.Model()|
    invariant s.Valid() && r.Valid()
    invariant {s} + s.Repr() !! {r} + r.Repr()

    invariant i <= ls
    invariant i <= lr
    invariant i + |s.Model()| == ls
    invariant i + |r.Model()| == lr
    invariant ms == ms[..i] + s.Model()
    invariant mr == mr[..i] + r.Model()
    invariant ms[..i] == mr[..i]

    invariant forall x {:trigger x in s.Repr(), x in old(s.Repr())} | x in s.Repr() - old(s.Repr()) :: fresh(x)
    invariant fresh(s.Repr()-old(s.Repr()))
    invariant forall x | x in s.Repr() :: allocated(x)
    invariant forall x {:trigger x in r.Repr(), x in old(r.Repr())} | x in r.Repr() - old(r.Repr()) :: fresh(x)
    invariant fresh(r.Repr()-old(r.Repr()))
    invariant forall x | x in r.Repr() :: allocated(x)
  {
    var x := s.Pop();
    var y := r.Pop();
    i := i + 1;
  }
  b := s.Empty() && r.Empty();
}

method FromArrayToStack(a: array<int>) returns (s: LinkedStack<int>)
  ensures s.Valid()
  ensures s.Model() == Seq.Rev(a[..])
  ensures forall u | u in s.Repr() :: fresh(u)
  ensures fresh(s.Repr())
  ensures forall x | x in s.Repr() :: allocated(x)
{
  s := new LinkedStack();
  PushFromArray(s, a);
}

/*
method {:timeLimitMultiplier 4} Main()
{
  var s:LinkedStack;
  var a := new int[2] (i => i);
  assert a[..] == [0, 1];
  s := FromArrayToStack(a);
  assert s.Model() == Seq.Rev([0, 1]) == [1, 0];
  var t: LinkedStack;
  var b := new int[3] (i => i+2);
  assert b[..] == [2, 3, 4];
  t := FromArrayToStack(b);
  assert t.Model() == Seq.Rev([2, 3, 4]) == [4, 3, 2];
  Extract(s, t);
  assert s.Model() == [];
  assert t.Model() == [0, 1] + [4, 3, 2] == [0, 1, 4, 3, 2];
}
*/

/*
// FAILS:
method Main() {
  var st: Stack := new LinkedStack();
  var st2: Stack := new LinkedStack();

  st.Push(3);
  var x := st.Pop();
  st.Push(2);
  st.Push(1);
  Print(st);
  st2.Push(3);
}
*/

/*
method Main() {
  var st: Stack := new LinkedStack();
  st.Push(3);
  st.Push(2);
  st.Push(1);
  Print(st);
}
*/

// Dafny program reordenando-la-cola-main.dfy compiled into C#
// To recompile, use 'csc' with: /r:System.Numerics.dll
// and choosing /target:exe or /target:library
// You might also want to include compiler switches like:
//     /debug /nowarn:0164 /nowarn:0219 /nowarn:1717 /nowarn:0162 /nowarn:0168

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"
// Dafny 2.3.0.10506
// Command Line Options: reordenando-la-cola-main.dfy Scan.cs
// reordenando-la-cola-main.dfy

method {:extern} Scan() returns (x: int)

method ScanArray(n: nat) returns (v: array<int>)
  ensures v.Length == n
  ensures fresh(v)
  decreases n
{
  v := new int[n];
  var i := 0;
  while i < n
    decreases n - i
  {
    v[i] := Scan();
    i := i + 1;
  }
}

method {:verify false} Main()
  decreases *
{
  while true
    decreases *
  {
    var n := Scan();
    if n == 0 {
      break;
    } else {
      var v := ScanArray(n);
      var neg := new Stack1();
      var pos := new Queue1();
      reordenandoLaCola(neg, pos, v);
      var i := 0;
      while i < n
        decreases n - i
      {
        print v[i];
        if i != n - 1 {
          print "" "";
        }
        i := i + 1;
      }
      print ""\n"";
    }
  }
}

lemma Allocated(s: set<object>)
  ensures forall x: object | x in s :: allocated(x)
  decreases s
{
}

lemma {:verify true} lemma1(v: array<int>, i: int)
  requires forall i: int | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i + 1])
  requires 0 <= i <= v.Length
  ensures forall j: int, k: int | 0 <= j < k < i :: abs(v[j]) <= abs(v[k])
  decreases v, i
{
}

method {:verify true} split(v: array<int>, neg: Stack, pos: Queue)
  requires v !in neg.Repr() && v !in pos.Repr()
  requires {pos} + pos.Repr() !! {neg} + neg.Repr()
  requires neg.Valid()
  requires pos.Valid()
  requires neg.Empty()
  requires pos.Empty()
  requires forall i: int | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i + 1])
  requires forall x: object | x in neg.Repr() :: allocated(x)
  requires forall x: object | x in pos.Repr() :: allocated(x)
  modifies pos, pos.Repr(), neg, neg.Repr()
  ensures v !in neg.Repr() && v !in pos.Repr()
  ensures {pos} + pos.Repr() !! {neg} + neg.Repr()
  ensures pos.Valid()
  ensures neg.Valid()
  ensures forall x: object | x in neg.Repr() - old(neg.Repr()) :: fresh(x)
  ensures forall x: int | x in neg.Model() :: x < 0
  ensures forall i: int | 0 <= i < |neg.Model()| - 1 :: abs(neg.Model()[i]) >= abs(neg.Model()[i + 1])
  ensures forall x: object | x in pos.Repr() - old(pos.Repr()) :: fresh(x)
  ensures forall x: int | x in pos.Model() :: x >= 0
  ensures forall i: int | 0 <= i < |pos.Model()| - 1 :: abs(pos.Model()[i]) <= abs(pos.Model()[i + 1])
  ensures Seq.MElems(neg.Model()) + Seq.MElems(pos.Model()) == Seq.MElems(v[..])
  ensures forall x: object | x in neg.Repr() :: allocated(x)
  ensures forall x: object | x in pos.Repr() :: allocated(x)
  decreases v, neg, pos
{
  var i := 0;
  while i < v.Length
    invariant i <= v.Length
    invariant forall i: int | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i + 1])
    invariant forall x: object | x in neg.Repr() - old(neg.Repr()) :: fresh(x)
    invariant forall x: object | x in pos.Repr() - old(pos.Repr()) :: fresh(x)
    invariant {pos} + pos.Repr() !! {neg} + neg.Repr()
    invariant neg.Valid()
    invariant pos.Valid()
    invariant forall x: int | x in neg.Model() :: x < 0
    invariant forall i: int | 0 <= i < |neg.Model()| - 1 :: abs(neg.Model()[i]) >= abs(neg.Model()[i + 1])
    invariant forall x: int | x in pos.Model() :: x >= 0
    invariant forall i: int | 0 <= i < |pos.Model()| - 1 :: abs(pos.Model()[i]) <= abs(pos.Model()[i + 1])
    invariant Seq.MElems(neg.Model()) + Seq.MElems(pos.Model()) == Seq.MElems(v[..i])
    invariant forall x: object | x in neg.Repr() :: allocated(x)
    invariant forall x: object | x in pos.Repr() :: allocated(x)
    decreases v.Length - i
  {
    lemma1(v, i + 1);
    assert forall j: int | 0 <= j < i :: abs(v[j]) <= abs(v[i]);
    if v[i] < 0 {
      if |neg.Model()| > 0 {
        assert neg.Model()[0] in Seq.MElems(neg.Model());
        assert neg.Model()[0] in Seq.MElems(neg.Model()) + Seq.MElems(pos.Model());
        assert neg.Model()[0] in Seq.MElems(v[..i]);
        assert neg.Model()[0] in v[..i];
        assert abs(v[i]) >= abs(neg.Model()[0]);
      }
      neg.Push(v[i]);
    } else {
      if |pos.Model()| > 0 {
        assert pos.Model()[|pos.Model()| - 1] in Seq.MElems(pos.Model());
        assert pos.Model()[|pos.Model()| - 1] in Seq.MElems(neg.Model()) + Seq.MElems(pos.Model());
        assert pos.Model()[|pos.Model()| - 1] in Seq.MElems(v[..i]);
        assert pos.Model()[|pos.Model()| - 1] in v[..i];
        assert abs(pos.Model()[|pos.Model()| - 1]) <= abs(v[i]);
      }
      pos.Enqueue(v[i]);
    }
    i := i + 1;
  }
  assert v[..i] == v[..];
}

method {:verify true} FillFromStack(r: array<int>, i: nat, st: Stack)
    returns (l: nat)
  requires st.Valid()
  requires {r} !! {st} + st.Repr()
  requires i + |st.Model()| <= r.Length
  requires forall x: object | x in st.Repr() :: allocated(x)
  modifies r, st, st.Repr()
  ensures st.Valid()
  ensures st.Empty()
  ensures forall x: object | x in st.Repr() - old(st.Repr()) :: fresh(x)
  ensures forall x: object | x in st.Repr() :: allocated(x)
  ensures r[..i] == old(r[..i])
  ensures r[i .. i + old(|st.Model()|)] == old(st.Model())
  ensures r[i + old(|st.Model()|)..] == old(r[i + |st.Model()|..])
  ensures l == i + old(|st.Model()|)
  ensures forall x: object | x in st.Repr() :: allocated(x)
  decreases r, i, st
{
  l := 0;
  while !st.Empty()
    invariant st.Valid()
    invariant {r} !! {st} + st.Repr()
    invariant forall x: object | x in st.Repr() - old(st.Repr()) :: fresh(x)
    invariant forall x: object | x in st.Repr() :: allocated(x)
    invariant 0 <= l <= old(|st.Model()|)
    invariant l == old(|st.Model()|) - |st.Model()|
    invariant st.Model() == old(st.Model()[l..])
    invariant r[..i] == old(r[..i])
    invariant r[i .. i + l] == old(st.Model()[..l])
    invariant r[i + old(|st.Model()|)..] == old(r[i + |st.Model()|..])
    decreases |st.Model()|
  {
    var x := st.Pop();
    r[i + l] := x;
    l := l + 1;
  }
  l := l + i;
}

method {:verify true} FillFromQueue(r: array<int>, i: nat, q: Queue)
    returns (l: nat)
  requires q.Valid()
  requires {r} !! {q} + q.Repr()
  requires i + |q.Model()| <= r.Length
  requires forall x: object | x in q.Repr() :: allocated(x)
  modifies r, q, q.Repr()
  ensures q.Valid()
  ensures q.Empty()
  ensures forall x: object | x in q.Repr() - old(q.Repr()) :: fresh(x)
  ensures forall x: object | x in q.Repr() :: allocated(x)
  ensures r[..i] == old(r[..i])
  ensures r[i .. i + old(|q.Model()|)] == old(q.Model())
  ensures r[i + old(|q.Model()|)..] == old(r[i + |q.Model()|..])
  ensures l == i + old(|q.Model()|)
  ensures forall x: object | x in q.Repr() :: allocated(x)
  decreases r, i, q
{
  l := 0;
  while !q.Empty()
    invariant q.Valid()
    invariant {r} !! {q} + q.Repr()
    invariant forall x: object | x in q.Repr() - old(q.Repr()) :: fresh(x)
    invariant forall x: object | x in q.Repr() :: allocated(x)
    invariant 0 <= l <= old(|q.Model()|)
    invariant l == old(|q.Model()|) - |q.Model()|
    invariant q.Model() == old(q.Model()[l..])
    invariant r[..i] == old(r[..i])
    invariant r[i .. i + l] == old(q.Model()[..l])
    invariant r[i + old(|q.Model()|)..] == old(r[i + |q.Model()|..])
    decreases |q.Model()|
  {
    var x := q.Dequeue();
    r[i + l] := x;
    l := l + 1;
  }
  l := l + i;
}

lemma {:verify true} LastLemma(neg: seq<int>, pos: seq<int>, s: seq<int>)
  requires forall x: int | x in neg :: x < 0
  requires forall i: int | 0 <= i < |neg| - 1 :: abs(neg[i]) >= abs(neg[i + 1])
  requires forall x: int | x in pos :: x >= 0
  requires forall i: int | 0 <= i < |pos| - 1 :: abs(pos[i]) <= abs(pos[i + 1])
  requires s == neg + pos
  ensures forall i: int | 0 <= i < |s| - 1 :: s[i] <= s[i + 1]
  decreases neg, pos, s
{
}

method {:verify true} reordenandoLaCola(neg: Stack, pos: Queue, v: array<int>)
  requires {v} !! {neg} + neg.Repr()
  requires {v} !! {pos} + pos.Repr()
  requires {pos} + pos.Repr() !! {neg} + neg.Repr()
  requires forall i: int | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i + 1])
  requires neg.Valid() && neg.Empty()
  requires pos.Valid() && pos.Empty()
  requires forall x: object | x in neg.Repr() :: allocated(x)
  requires forall x: object | x in pos.Repr() :: allocated(x)
  modifies v, neg, neg.Repr(), pos, pos.Repr()
  ensures neg.Valid()
  ensures pos.Valid()
  ensures {v} !! {neg} + neg.Repr()
  ensures {v} !! {pos} + pos.Repr()
  ensures {pos} + pos.Repr() !! {neg} + neg.Repr()
  ensures forall x: object | x in neg.Repr() - old(neg.Repr()) :: fresh(x)
  ensures forall x: object | x in neg.Repr() :: allocated(x)
  ensures forall x: object | x in pos.Repr() - old(pos.Repr()) :: fresh(x)
  ensures forall x: object | x in pos.Repr() :: allocated(x)
  ensures Array.melems(v) == old(Array.melems(v))
  ensures forall i: int | 0 <= i < v.Length - 1 :: v[i] <= v[i + 1]
  decreases neg, pos, v
{
  split(v, neg, pos);
  ghost var negmodel := neg.Model();
  ghost var posmodel := pos.Model();
  calc == {
    |negmodel| + |posmodel|;
    |Seq.MElems(negmodel)| + |Seq.MElems(posmodel)|;
    |Seq.MElems(negmodel) + Seq.MElems(posmodel)|;
    |Seq.MElems(v[..])|;
    |v[..]|;
    v.Length;
  }
  var i := 0;
  i := FillFromStack(v, i, neg);
  i := FillFromQueue(v, i, pos);
  LastLemma(negmodel, posmodel, v[..]);
}

method EvalPostfix(s: string) returns (res: int)
  requires forall c: char | c in s :: c in ""0123456789+-*//*""
  decreases s
{
  var st: Stack := new Stack1();
  var i := 0;
  while i < |s|
    invariant forall x: object | x in st.Repr() :: fresh(x)
    invariant st.Valid()
    decreases |s| - i
  {
    var c := s[0];
    if c in ""0123456789"" {
      st.Push(c as int - 48);
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
  decreases c
{
  if c == ')' then
    '('
  else if c == ']' then
    '['
  else
    '{'
}

method BalancedTest(s: string) returns (b: bool)
  decreases s
{
  var st: Stack := new Stack1();
  var i := 0;
  while i < |s|
    invariant forall x: object | x in st.Repr() :: fresh(x)
    invariant st.Valid()
    decreases |s| - i
  {
    if s[i] == '(' || s[i] == '[' || s[i] == '{' {
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
  requires st.Valid()
  modifies st, st.Repr()
  ensures st.Valid()
  ensures st.Empty()
  decreases st
{
  while !st.Empty()
    invariant st.Valid()
    invariant forall x: object | x in st.Repr() - old(st.Repr()) :: fresh(x)
    decreases |st.Model()|
  {
    var x := st.Pop();
    print x;
    print ""\n"";
  }
}

function method BigUnion<A>(S: set<set<A>>): set<A>
  decreases S
{
  set X: set<A>, x: A {:trigger x in X} | X in S && x in X :: x
}

function method abs(x: int): int
  decreases x
{
  if x < 0 then
    -x
  else
    x
}

class Stack1 extends Stack {
  var list: List<int>

  function Depth(): nat
  {
    1
  }

  function Repr0(): set<object>
    reads this
    decreases {this}
  {
    {list}
  }

  function Repr1(): set<object>
    reads this, Repr0()
    decreases Repr0() + {this}
  {
    {list} + list.Repr()
  }

  function ReprFamily(n: nat): set<object>
    reads this, if n == 0 then {} else ReprFamily(n - 1)
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n - 1)
    decreases n
  {
    if n == 0 then
      Repr0()
    else if n == 1 then
      Repr1()
    else
      ReprFamily(n - 1)
  }

  lemma UselessLemma()
    ensures Repr() == ReprFamily(1)
  {
  }

  predicate Valid()
    reads this, Repr()
    decreases Repr() + {this}
  {
    list.Valid()
  }

  function Model(): seq<int>
    requires Valid()
    reads this, list, list.spine
    decreases (set _s2s_0: SNode<int> | _s2s_0 in list.spine :: _s2s_0) + {this, list}
  {
    list.Model()
  }

  constructor ()
    ensures Valid()
    ensures Model() == []
    ensures forall x: object | x in Repr() :: fresh(x)
    ensures forall x: object | x in Repr() :: allocated(x)
  {
    list := new List<int>();
  }

  function method Empty(): bool
    requires Valid()
    reads this, Repr()
    ensures Empty() <==> Model() == []
    decreases Repr() + {this}
  {
    list.head == null
  }

  method Top() returns (x: int)
    requires Valid()
    requires Model() != []
    ensures x == Model()[0]
  {
    x := list.head.data;
  }

  method Push(x: int)
    requires Valid()
    modifies list
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures list == old(list)
    decreases x
  {
    list.Push(x);
  }

  method Pop() returns (x: int)
    requires list.head != null
    requires Valid()
    modifies list
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
  {
    x := list.Pop();
  }
}

class Queue1 extends Queue {
  var list: DoublyLinkedListWithLast

  function Depth(): nat
    ensures Depth() > 0
  {
    2
  }

  function Repr0(): set<object>
    reads this
    decreases {this}
  {
    {list}
  }

  function Repr1(): set<object>
    reads this, Repr0()
    decreases Repr0() + {this}
  {
    Repr0() + {list.list}
  }

  function Repr2(): set<object>
    reads this, Repr1()
    decreases Repr1() + {this}
  {
    Repr1() + list.Repr()
  }

  function ReprFamily(n: nat): set<object>
    requires n <= Depth()
    reads this, if n == 0 then {} else ReprFamily(n - 1)
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n - 1)
    decreases n
  {
    if n == 0 then
      Repr0()
    else if n == 1 then
      Repr1()
    else if n == 2 then
      Repr2()
    else
      assert false; {}
  }

  predicate Valid()
    reads this, Repr()
    decreases Repr() + {this}
  {
    list.Valid()
  }

  function Model(): seq<int>
    requires Valid()
    reads this, Repr()
    decreases Repr() + {this}
  {
    list.Model()
  }

  function method Empty(): bool
    requires Valid()
    reads this, Repr()
    ensures Empty() <==> Model() == []
    decreases Repr() + {this}
  {
    list.list.head == null
  }

  constructor ()
    ensures Valid()
    ensures Model() == []
    ensures forall x: object | x in Repr() :: fresh(x)
    ensures forall x: object | x in Repr() :: allocated(x)
  {
    list := new DoublyLinkedListWithLast();
  }

  method Front() returns (x: int)
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[0]
  {
    x := list.Front();
  }

  method Enqueue(x: int)
    requires Valid()
    modifies Repr()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    decreases x
  {
    list.PushBack(x);
  }

  method Dequeue() returns (x: int)
    requires Valid()
    requires Model() != []
    modifies Repr()
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
  {
    x := list.PopFront();
  }
}

class QueueIterator {
  ghost var index: nat
  ghost var parent: Queue1
  var node: DNode?

  predicate Valid()
    reads this, parent, parent.Repr()
    decreases parent.Repr() + {this, parent}
  {
    parent.Valid() &&
    (node != null ==>
      node in parent.list.list.Repr() &&
      index == parent.list.list.GetIndex(node))
  }

  constructor (l: Queue1)
    requires l.Valid()
    ensures Valid()
    ensures parent == l
    decreases l
  {
    index := 0;
    parent := l;
    node := l.list.list.head;
  }

  function method HasNext(): bool
    reads this
    decreases {this}
  {
    node != null
  }

  method Next() returns (x: int)
    requires HasNext()
    requires Valid()
    modifies this
    ensures Valid()
    ensures x == old(parent.Model()[index])
    ensures old(index) < index
    ensures parent == old(parent)
  {
    {
      parent.list.list.ModelRelationWithSpine();
      if index < |parent.list.list.spine| - 1 {
        assert parent.list.list.spine[index + 1] == parent.list.list.spine[index].next;
      }
    }
    x := node.data;
    index := index + 1;
    node := node.next;
  }
}

module Array {
  function method elems<A>(l: array<A>): set<A>
    reads l
    decreases {l}, l
  {
    set x: A {:trigger x in l[..]} | x in l[..]
  }

  function method melems<A>(l: array<A>): multiset<A>
    reads l
    decreases {l}, l
  {
    multiset(l[..])
  }
}

module Seq {
  function Rev<A>(xs: seq<A>): seq<A>
    ensures |xs| == |Rev(xs)|
    decreases xs
  {
    if |xs| == 0 then
      []
    else
      Rev(xs[1..]) + [xs[0]]
  }

  lemma /*{:_induction xs}*/ LeRev(xs: seq<int>)
    requires forall i: int | 0 <= i < |xs| - 1 :: xs[i] >= xs[i + 1]
    ensures forall i: int | 0 <= i < |xs| - 1 :: Rev(xs)[i] <= Rev(xs)[i + 1]
    decreases xs
  {
  }

  function Map<A, B>(f: A -> B, xs: seq<A>): seq<B>
    reads set x: A, o: object {:trigger o in f.reads(x)} | x in xs && o in f.reads(x) :: o
    decreases set x: A, o: object {:trigger o in f.reads(x)} | x in xs && o in f.reads(x) :: o, xs
  {
    if xs == [] then
      []
    else
      [f(xs[0])] + Map(f, xs[1..])
  }

  function Elems<A>(xs: seq<A>): set<A>
    decreases xs
  {
    set x: A {:trigger x in xs} | x in xs
  }

  lemma /*{:_induction l}*/ ElemsRev<A>(l: seq<A>)
    ensures Elems(Rev(l)) == Elems(l)
    ensures forall x: A | x in Rev(l) :: x in l
    ensures forall x: A | x in l :: x in Rev(l)
    decreases l
  {
  }

  lemma /*{:_induction l}*/ MElemsRev<A>(l: seq<A>)
    ensures MElems(Rev(l)) == MElems(l)
    decreases l
  {
  }

  function MElems<A>(xs: seq<A>): multiset<A>
    decreases xs
  {
    multiset(xs)
  }

  lemma InEquivInMultiset<A>(xs: seq<A>)
    ensures forall x: A :: x in xs <==> x in multiset(xs)
    decreases xs
  {
  }

  function Insert<A>(x: A, xs: seq<A>, i: nat): seq<A>
    requires 0 <= i <= |xs|
    ensures i == 0 ==> Insert(x, xs, i) == [x] + xs
    ensures i == |xs| ==> Insert(x, xs, i) == xs + [x]
    decreases xs, i
  {
    xs[..i] + [x] + xs[i..]
  }

  function Remove<A>(xs: seq<A>, i: nat): seq<A>
    requires 0 <= i < |xs|
    ensures i == 0 ==> Remove(xs, i) == xs[1..]
    ensures i == |xs| ==> Remove(xs, i) == xs[..|xs| - 1]
    decreases xs, i
  {
    xs[..i] + xs[i + 1..]
  }
}

trait Stack {
  function Depth(): nat
    ensures Depth() > 0

  function ReprFamily(n: nat): set<object>
    requires n <= Depth()
    reads this, if n == 0 then {} else ReprFamily(n - 1)
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n - 1)
    decreases n

  function Repr(): set<object>
    reads this, ReprFamily(Depth() - 1)
    decreases ReprFamily(Depth() - 1) + {this}
  {
    ReprFamily(Depth())
  }

  lemma UselessLemma()
    ensures Repr() == ReprFamily(Depth())

  predicate Valid()
    reads this, Repr()
    decreases Repr() + {this}

  function Model(): seq<int>
    requires Valid()
    reads this, Repr()
    decreases Repr() + {this}

  function method Empty(): bool
    requires Valid()
    reads this, Repr()
    ensures Empty() <==> Model() == []
    decreases Repr() + {this}

  method Top() returns (x: int)
    requires Valid()
    requires !Empty()
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[0]

  method Push(x: int)
    requires Valid()
    modifies Repr()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures forall x: object | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x: object | x in Repr() :: allocated(x)
    decreases x

  method Pop() returns (x: int)
    requires Valid()
    requires !Empty()
    modifies Repr()
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures forall x: object | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x: object | x in Repr() :: allocated(x)
}

trait Queue {
  function Depth(): nat
    ensures Depth() > 0

  function ReprFamily(n: nat): set<object>
    requires n <= Depth()
    reads this, if n == 0 then {} else ReprFamily(n - 1)
    ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n - 1)
    decreases n

  function Repr(): set<object>
    reads this, ReprFamily(Depth() - 1)
    decreases ReprFamily(Depth() - 1) + {this}
  {
    ReprFamily(Depth())
  }

  predicate Valid()
    reads this, Repr()
    decreases Repr() + {this}

  function Model(): seq<int>
    requires Valid()
    reads this, Repr()
    decreases Repr() + {this}

  function method Empty(): bool
    requires Valid()
    reads this, Repr()
    ensures Empty() <==> Model() == []
    decreases Repr() + {this}

  method Front() returns (x: int)
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[0]

  method Enqueue(x: int)
    requires Valid()
    modifies Repr()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
    ensures forall x: object | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x: object | x in Repr() :: allocated(x)
    decreases x

  method Dequeue() returns (x: int)
    requires Valid()
    requires Model() != []
    modifies Repr()
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures forall x: object | x in Repr() - old(Repr()) :: fresh(x)
    ensures forall x: object | x in Repr() :: allocated(x)
}

class SNode<A> {
  var data: A
  var next: SNode?<A>

  constructor (data: A, next: SNode?<A>)
    ensures this.data == data
    ensures this.next == next
    decreases next
  {
    this.data := data;
    this.next := next;
  }

  predicate IsPrevOf(n: SNode<A>)
    reads this
    decreases {this}, n
  {
    next == n
  }
}

class List<A> {
  var head: SNode?<A>
  ghost var spine: seq<SNode<A>>

  function Repr(): set<object>
    reads this
    decreases {this}
  {
    set x: object {:trigger x in spine} | x in spine
  }

  predicate Valid()
    reads this, Repr()
    decreases Repr() + {this}
  {
    (forall i: int | 0 <= i < |spine| - 1 :: 
      spine[i].IsPrevOf(spine[i + 1])) &&
    if head == null then spine == [] else spine != [] && spine[0] == head && spine[|spine| - 1].next == null
  }

  lemma HeadInSpine()
    requires Valid()
    ensures head != null ==> head in spine
  {
  }

  lemma DistinctSpineAux(n: nat)
    requires Valid()
    requires 0 <= n <= |spine|
    ensures forall i: int, j: int | n <= i < j < |spine| :: spine[i] != spine[j]
    decreases |spine| - n
  {
  }

  lemma DistinctSpine()
    requires Valid()
    ensures forall i: int, j: int | 0 <= i < j < |spine| :: spine[i] != spine[j]
  {
  }

  lemma HeadNotInTail()
    requires Valid()
    requires head != null
    ensures head !in spine[1..]
  {
  }

  lemma NextNullImpliesLast(n: SNode<A>)
    requires Valid()
    requires n in spine
    requires n.next == null
    ensures spine[|spine| - 1] == n
    decreases n
  {
  }

  lemma HeadNextNullImpliesSingleton()
    requires Valid()
    requires head != null
    requires head.next == null
    ensures spine == [head]
  {
  }

  static function ModelAux(xs: seq<SNode<A>>): seq<A>
    reads set x: SNode<A> {:trigger x in xs} | x in xs :: x`data
    decreases set x: SNode<A> {:trigger x in xs} | x in xs :: x, xs
  {
    if xs == [] then
      []
    else
      assert xs[0] in xs; assert forall x: SNode<A> | x in xs[1..] :: x in xs; [xs[0].data] + ModelAux(xs[1..])
  }

  lemma /*{:_induction xs, ys}*/ ModelAuxCommutesConcat(xs: seq<SNode<A>>, ys: seq<SNode<A>>)
    ensures ModelAux(xs + ys) == ModelAux(xs) + ModelAux(ys)
    decreases xs, ys
  {
  }

  static lemma /*{:_induction spine}*/ ModelRelationWithSpineAux(spine: seq<SNode<A>>, model: seq<A>)
    requires ModelAux(spine) == model
    ensures |spine| == |model|
    ensures forall i: int | 0 <= i < |spine| :: spine[i].data == model[i]
    decreases spine, model
  {
  }

  lemma ModelRelationWithSpine()
    requires Valid()
    ensures |spine| == |Model()|
    ensures forall i: int | 0 <= i < |spine| :: spine[i].data == Model()[i]
  {
  }

  function Model(): seq<A>
    requires Valid()
    reads this, spine
    decreases (set _s2s_0: SNode<A> | _s2s_0 in spine :: _s2s_0) + {this}
  {
    ModelAux(spine)
  }

  static function ModelUntilAux(xs: seq<SNode<A>>, last: SNode<A>): seq<A>
    reads set x: SNode<A> {:trigger x in xs} | x in xs :: x`data
    decreases set x: SNode<A> {:trigger x in xs} | x in xs :: x, xs, last
  {
    if xs == [] || xs[0] == last then
      []
    else
      assert xs[0] in xs; assert forall x: SNode<A> | x in xs[1..] :: x in xs; [xs[0].data] + ModelUntilAux(xs[1..], last)
  }

  function ModelUntil(last: SNode<A>): seq<A>
    reads this, spine
    decreases (set _s2s_0: SNode<A> | _s2s_0 in spine :: _s2s_0) + {this}, last
  {
    ModelUntilAux(spine, last)
  }

  function GetIndex(n: SNode<A>): nat
    requires Valid()
    requires n in Repr()
    reads this, spine
    ensures 0 <= GetIndex(n) < |spine|
    ensures 0 <= GetIndex(n) < |Model()|
    ensures spine[GetIndex(n)] == n
    ensures forall i: int | 0 <= i < |spine| && spine[i] == n :: i == GetIndex(n)
    decreases (set _s2s_0: SNode<A> | _s2s_0 in spine :: _s2s_0) + {this}, n
  {
    ModelRelationWithSpine();
    DistinctSpine();
    var i: int :| 0 <= i < |spine| && spine[i] == n;
    i
  }

  lemma LastHasLastIndex(last: SNode<A>)
    requires Valid()
    requires last.next == null
    requires last in Repr()
    ensures GetIndex(last) == |spine| - 1
    decreases last
  {
  }

  lemma PrevHasPrevIndex(prev: SNode<A>, node: SNode<A>)
    requires Valid()
    requires prev in Repr()
    requires node in Repr()
    requires prev.IsPrevOf(node)
    ensures GetIndex(prev) == GetIndex(node) - 1
    decreases prev, node
  {
  }

  constructor ()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    head := null;
    spine := [];
  }

  method PopNode() returns (h: SNode<A>)
    requires Valid()
    requires Model() != []
    modifies this
    ensures Valid()
    ensures [h] + spine == old(spine)
    ensures Repr() + {h} == old(Repr())
    ensures [h.data] + Model() == old(Model())
    ensures Repr() < old(Repr())
  {
    h := head;
    {
      if head.next == null {
        HeadNextNullImpliesSingleton();
      }
      HeadNotInTail();
    }
    head := head.next;
    spine := spine[1..];
    assert old(spine[0]) !in Repr();
    assert old(spine[0]) in old(Repr());
    assert Repr() < old(Repr());
  }

  method Pop() returns (res: A)
    requires Valid()
    requires Model() != []
    modifies this
    ensures Valid()
    ensures [res] + Model() == old(Model())
    ensures Repr() < old(Repr())
    ensures spine == old(spine[1..])
  {
    var tmp := PopNode();
    res := tmp.data;
  }

  method PushNode(h: SNode<A>)
    requires Valid()
    requires h !in Repr()
    modifies this, h`next
    ensures Valid()
    ensures spine == [h] + old(spine)
    ensures Model() == [h.data] + old(Model())
    ensures Repr() > old(Repr())
    ensures Repr() == old(Repr()) + {h}
    decreases h
  {
    h.next := head;
    head := h;
    spine := [head] + spine;
    assert head !in old(Repr());
  }

  method Push(x: A)
    requires Valid()
    modifies this
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures spine[1..] == old(spine)
  {
    var n := new SNode<A>(x, null);
    PushNode(n);
  }

  method Append(other: List<A>)
    requires Valid()
    requires other.Valid()
    requires Repr() !! other.Repr()
    modifies this, Repr(), other
    ensures Valid()
    ensures Model() == old(Model() + other.Model())
    ensures Repr() == old(Repr() + other.Repr())
    ensures other.Valid()
    ensures other.Model() == []
    ensures other.Repr() == {}
    decreases other
  {
    if head == null {
      head := other.head;
      spine := other.spine;
    } else {
      var last := head;
      ghost var i := 0;
      while last.next != null
        invariant last != null
        invariant 0 <= i < |spine|
        invariant spine[i] == last
        decreases |spine| - i
      {
        last := last.next;
        i := i + 1;
      }
      NextNullImpliesLast(last);
      last.next := other.head;
      spine := spine + other.spine;
      ModelAuxCommutesConcat(old(spine), other.spine);
    }
    other.head := null;
    other.spine := [];
  }

  method PopPush(other: List<A>)
    requires head != null
    requires Valid()
    requires other.Valid()
    requires Repr() !! other.Repr()
    modifies this, other, Repr(), other.Repr()
    ensures Repr() !! other.Repr()
    ensures Valid()
    ensures other.Valid()
    ensures old(Repr()) > Repr()
    ensures Repr() + {old(head)} == old(Repr())
    ensures old(other.Repr()) < other.Repr()
    ensures other.Repr() == old(other.Repr()) + {old(head)}
    ensures Seq.Rev(old(Model())) + old(other.Model()) == Seq.Rev(Model()) + other.Model()
    decreases other
  {
    var n := PopNode();
    other.PushNode(n);
  }

  method Reverse()
    requires Valid()
    modifies this, Repr()
    ensures Valid()
    ensures Model() == Seq.Rev(old(Model()))
    ensures Repr() == old(Repr())
  {
    var aux := new List<A>();
    aux.head := head;
    aux.spine := spine;
    head := null;
    spine := [];
    while aux.head != null
      invariant Valid()
      invariant aux.Valid()
      invariant Seq.Rev(old(Model())) == Seq.Rev(aux.Model()) + Model()
      invariant Repr() !! aux.Repr()
      invariant old(Repr()) == Repr() + aux.Repr()
      decreases aux.Repr()
    {
      aux.PopPush(this);
    }
  }

  method Insert(mid: SNode<A>, x: A)
    requires Valid()
    requires mid in Repr()
    modifies this, mid
    ensures Valid()
    ensures spine == Seq.Insert(mid.next, old(spine), old(GetIndex(mid)) + 1)
    ensures Model() == Seq.Insert(x, old(Model()), old(GetIndex(mid)) + 1)
    ensures mid.next != null
    ensures fresh(mid.next)
    ensures mid.next in spine
    ensures mid.next.next == old(mid.next)
    ensures forall n: SNode<A> | n in old(spine) :: n in spine
    decreases mid
  {
    {
      DistinctSpine();
      ModelRelationWithSpine();
    }
    var n := new SNode<A>(x, mid.next);
    mid.next := n;
    {
      ghost var i :| 0 <= i < |spine| && spine[i] == mid;
      spine := spine[..i + 1] + [n] + spine[i + 1..];
      assert Valid();
      ModelRelationWithSpine();
    }
  }

  method RemoveNext(mid: SNode<A>)
    requires Valid()
    requires mid in Repr()
    requires mid.next != null
    modifies this, mid
    ensures Valid()
    ensures spine == Seq.Remove(old(spine), old(GetIndex(mid)) + 1)
    ensures old(GetIndex(mid)) + 1 < old(|Model()|)
    ensures Model() == Seq.Remove(old(Model()), old(GetIndex(mid) + 1))
    ensures mid.next == old(mid.next.next)
    ensures forall n: SNode<A> | n in old(spine) && n != old(mid.next) :: n in spine
    decreases mid
  {
    {
      DistinctSpine();
      ModelRelationWithSpine();
    }
    ghost var i :| 0 <= i < |spine| && spine[i] == mid;
    assert spine[i + 1] == mid.next;
    assert i + 2 < |spine| ==> spine[i + 2] == mid.next.next;
    mid.next := mid.next.next;
    {
      spine := spine[..i + 1] + spine[i + 2..];
      assert GetIndex(mid) == old(GetIndex(mid));
      ModelRelationWithSpine();
      assert Model() == old(Seq.Remove(Model(), GetIndex(mid) + 1));
    }
  }

  method FindPrev(mid: SNode<A>) returns (prev: SNode<A>)
    requires Valid()
    requires head != mid
    requires mid in Repr()
    ensures prev in Repr()
    ensures prev.next == mid
    decreases mid
  {
    prev := head;
    ghost var i := 0;
    while prev.next != mid
      invariant 0 <= i < |spine|
      invariant mid in spine[i + 1..]
      invariant spine[i] == prev
      decreases |spine| - i
    {
      assert spine[i + 1] == prev.next;
      prev := prev.next;
      i := i + 1;
    }
  }
}

class DoublyLinkedListWithLast {
  var list: DoublyLinkedList
  var last: DNode?

  predicate Valid()
    reads this, list, list.spine
    decreases (set _s2s_0: DNode | _s2s_0 in list.spine :: _s2s_0) + {this, list}
  {
    list.Valid() &&
    if last == null then list.head == null else last in list.Repr() && last.next == null
  }

  function Repr(): set<object>
    reads this, list
    decreases {this, list}
  {
    list.Repr()
  }

  function Model(): seq<A>
    requires Valid()
    reads this, list, list.spine
    decreases (set _s2s_0: DNode | _s2s_0 in list.spine :: _s2s_0) + {this, list}
  {
    list.Model()
  }

  constructor ()
    ensures Valid()
    ensures Model() == []
    ensures fresh(list)
    ensures last == null
    ensures fresh(Repr())
  {
    list := new DoublyLinkedList();
    last := null;
  }

  method Front() returns (x: int)
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[0]
  {
    x := list.head.data;
  }

  method Back() returns (x: int)
    requires Valid()
    requires Model() != []
    ensures Valid()
    ensures Model() == old(Model())
    ensures x == Model()[|Model()| - 1]
  {
    list.LastHasLastIndex(last);
    list.ModelRelationWithSpine();
    x := last.data;
  }

  method PushFront(x: A)
    requires Valid()
    modifies this, list, Repr()
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures list == old(list)
    decreases x
  {
    var ohead := list.head;
    {
      if ohead != null {
        list.LastHasLastIndex(last);
      }
    }
    list.PushFront(x);
    if ohead == null {
      last := list.head;
    }
  }

  method PopFront() returns (x: A)
    requires Valid()
    requires Model() != []
    modifies this, list, Repr()
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
    ensures list == old(list)
  {
    {
      if list.head != null {
        list.LastHasLastIndex(last);
      }
    }
    if list.head == last {
      last := null;
    }
    {
      if list.head.next != null {
        assert list.head == list.spine[0];
        assert list.head.next == list.spine[1];
        assert list.head.next in Repr();
      }
    }
    x := list.PopFront();
  }

  method PushBack(x: A)
    requires Valid()
    modifies this, list, Repr()
    ensures Valid()
    ensures Model() == old(Model()) + [x]
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures list == old(list)
    decreases x
  {
    if last == null {
      assert Model() == [];
      list.PushFront(x);
      last := list.head;
    } else {
      {
        list.LastHasLastIndex(last);
        list.ModelRelationWithSpine();
      }
      list.Insert(last, x);
      last := last.next;
      assert last != null;
      assert Valid();
    }
  }

  method PopBack() returns (x: A)
    requires Valid()
    requires Model() != []
    modifies this, list, list.Repr()
    ensures Valid()
    ensures Model() + [x] == old(Model())
    ensures Repr() < old(Repr())
    ensures list == old(list)
  {
    if list.head == last {
      assert list.head.next == null;
      list.HeadNextNullImpliesSingleton();
      assert list.spine == [list.head];
      calc == {
        list.Model();
        list.ModelAux(list.spine);
        [list.head.data];
      }
      x := list.head.data;
      list.head := null;
      list.spine := [];
      last := null;
      assert old(list.Model()) == [x];
      assert Model() + [x] == old(Model());
      assert Repr() < old(Repr());
    } else {
      x := last.data;
      var prev := last.prev;
      {
        list.ModelRelationWithSpine();
        list.LastHasLastIndex(last);
        assert last == list.spine[|list.spine| - 1];
        assert last.prev == list.spine[|list.spine| - 2];
        assert prev in Repr();
        assert last in Repr();
      }
      list.RemoveNext(prev);
      last := prev;
    }
  }
}

type A = int

class DNode {
  var prev: DNode?
  var data: A
  var next: DNode?

  constructor (prev: DNode?, data: A, next: DNode?)
    ensures this.prev == prev
    ensures this.data == data
    ensures this.next == next
    decreases prev, data, next
  {
    this.prev := prev;
    this.data := data;
    this.next := next;
  }

  predicate IsPrevOf(n: DNode)
    reads this
    decreases {this}, n
  {
    next == n
  }

  predicate IsNextOf(n: DNode)
    reads this
    decreases {this}, n
  {
    prev == n
  }
}

class DoublyLinkedList {
  var head: DNode?
  ghost var spine: seq<DNode>

  function Repr(): set<object>
    reads this
    decreases {this}
  {
    set x: object {:trigger x in spine} | x in spine
  }

  predicate Valid()
    reads this, Repr()
    decreases Repr() + {this}
  {
    (forall i: int | 0 <= i < |spine| - 1 :: 
      spine[i].next == spine[i + 1] &&
      spine[i + 1].prev == spine[i]) &&
    if head == null then spine == [] else spine != [] && spine[0] == head && spine[0].prev == null && spine[|spine| - 1].next == null
  }

  lemma DistinctSpineAux(n: nat)
    requires Valid()
    requires 0 <= n <= |spine|
    ensures forall i: int, j: int | n <= i < j < |spine| :: spine[i] != spine[j]
    decreases |spine| - n
  {
  }

  lemma DistinctSpine()
    requires Valid()
    ensures forall i: int, j: int | 0 <= i < j < |spine| :: spine[i] != spine[j]
  {
  }

  static function ModelAux(xs: seq<DNode>): seq<A>
    reads set x: DNode {:trigger x in xs} | x in xs :: x`data
    decreases set x: DNode {:trigger x in xs} | x in xs :: x, xs
  {
    if xs == [] then
      []
    else
      assert xs[0] in xs; assert forall x: DNode | x in xs[1..] :: x in xs; [xs[0].data] + ModelAux(xs[1..])
  }

  lemma HeadNextNullImpliesSingleton()
    requires Valid()
    requires head != null
    requires head.next == null
    ensures spine == [head]
  {
  }

  function Model(): seq<A>
    requires Valid()
    reads this, spine
    decreases (set _s2s_0: DNode | _s2s_0 in spine :: _s2s_0) + {this}
  {
    ModelAux(spine)
  }

  constructor ()
    ensures Valid()
    ensures Model() == []
    ensures fresh(Repr())
  {
    head := null;
    spine := [];
  }

  static lemma /*{:_induction spine}*/ ModelRelationWithSpineAux(spine: seq<DNode>, model: seq<A>)
    requires ModelAux(spine) == model
    ensures |spine| == |model|
    ensures forall i: int | 0 <= i < |spine| :: spine[i].data == model[i]
    decreases spine, model
  {
  }

  lemma ModelRelationWithSpine()
    requires Valid()
    ensures |spine| == |Model()|
    ensures forall i: int | 0 <= i < |spine| :: spine[i].data == Model()[i]
  {
  }

  function GetIndex(n: DNode): nat
    requires Valid()
    requires n in Repr()
    reads this, spine
    ensures 0 <= GetIndex(n) < |spine|
    ensures 0 <= GetIndex(n) < |Model()|
    ensures spine[GetIndex(n)] == n
    ensures forall i: int | 0 <= i < |spine| && spine[i] == n :: i == GetIndex(n)
    decreases (set _s2s_0: DNode | _s2s_0 in spine :: _s2s_0) + {this}, n
  {
    ModelRelationWithSpine();
    DistinctSpine();
    var i: int :| 0 <= i < |spine| && spine[i] == n;
    i
  }

  lemma LastHasLastIndex(last: DNode)
    requires Valid()
    requires last.next == null
    requires last in Repr()
    ensures GetIndex(last) == |spine| - 1
    decreases last
  {
  }

  lemma PrevHasPrevIndex(prev: DNode, node: DNode)
    requires Valid()
    requires prev in Repr()
    requires node in Repr()
    requires prev.IsPrevOf(node)
    ensures GetIndex(prev) == GetIndex(node) - 1
    decreases prev, node
  {
  }

  method PopFront() returns (x: A)
    requires Valid()
    requires Model() != []
    modifies this, head.next
    ensures Valid()
    ensures [x] + Model() == old(Model())
    ensures Repr() < old(Repr())
    ensures spine == old(spine[1..])
  {
    DistinctSpine();
    assert head in Repr();
    if head.next == null {
      HeadNextNullImpliesSingleton();
    } else {
      assert head == spine[0];
      assert head.IsPrevOf(spine[1]);
      assert spine[1] == head.next;
      assert head.next in Repr();
    }
    x := head.data;
    head := head.next;
    spine := spine[1..];
    if head != null {
      head.prev := null;
    }
  }

  method PushFront(x: A)
    requires Valid()
    modifies this, head
    ensures Valid()
    ensures Model() == [x] + old(Model())
    ensures Repr() > old(Repr())
    ensures fresh(Repr() - old(Repr()))
    ensures spine[1..] == old(spine)
    decreases x
  {
    var n := new DNode(null, x, head);
    if head != null {
      head.prev := n;
    }
    head := n;
    spine := [head] + spine;
    assert head !in old(Repr());
  }

  method Insert(mid: DNode, x: A)
    requires Valid()
    requires mid in Repr()
    modifies this, Repr()
    ensures Valid()
    ensures spine == Seq.Insert(mid.next, old(spine), old(GetIndex(mid)) + 1)
    ensures Model() == Seq.Insert(x, old(Model()), old(GetIndex(mid)) + 1)
    ensures mid.next != null
    ensures fresh(mid.next)
    ensures mid.next in spine
    ensures mid.next.next == old(mid.next)
    ensures forall n: DNode | n in old(spine) :: n in spine
    decreases mid, x
  {
    {
      DistinctSpine();
      ModelRelationWithSpine();
    }
    var n := new DNode(mid, x, mid.next);
    assert n.prev == mid;
    assert n.prev == mid;
    ghost var i :| 0 <= i < |spine| && spine[i] == mid;
    if mid.next != null {
      assert spine[i + 1] == mid.next;
      assert mid.next in Repr();
      mid.next.prev := n;
    }
    mid.next := n;
    {
      spine := spine[..i + 1] + [n] + spine[i + 1..];
      ModelRelationWithSpine();
    }
  }

  method RemoveNext(mid: DNode)
    requires Valid()
    requires mid in Repr()
    requires mid.next != null
    modifies this, Repr()
    ensures Valid()
    ensures spine == Seq.Remove(old(spine), old(GetIndex(mid)) + 1)
    ensures old(GetIndex(mid)) + 1 < old(|Model()|)
    ensures Model() == Seq.Remove(old(Model()), old(GetIndex(mid) + 1))
    ensures mid.next == old(mid.next.next)
    ensures forall n: DNode | n in old(spine) && n != old(mid.next) :: n in spine
    decreases mid
  {
    {
      DistinctSpine();
      ModelRelationWithSpine();
    }
    ghost var i :| 0 <= i < |spine| && spine[i] == mid;
    assert spine[i + 1] == mid.next;
    assert i + 2 < |spine| ==> spine[i + 2] == mid.next.next;
    mid.next := mid.next.next;
    if mid.next != null {
      mid.next.prev := mid;
    }
    {
      spine := spine[..i + 1] + spine[i + 2..];
      assert Valid();
      ModelRelationWithSpine();
      assert Valid();
      assert GetIndex(mid) == old(GetIndex(mid));
      assert Model() == old(Seq.Remove(Model(), GetIndex(mid) + 1));
    }
  }

  method FindPrev(mid: DNode) returns (prev: DNode)
    requires Valid()
    requires head != mid
    requires mid in Repr()
    ensures prev in Repr()
    ensures prev.next == mid
    decreases mid
  {
    prev := head;
    ghost var i := 0;
    while prev.next != mid
      invariant 0 <= i < |spine|
      invariant mid in spine[i + 1..]
      invariant spine[i] == prev
      decreases |spine| - i
    {
      assert spine[i + 1] == prev.next;
      prev := prev.next;
      i := i + 1;
    }
  }
}
")]

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny
{
  using System.Collections.Generic;
  // set this option if you want to use System.Collections.Immutable and if you know what you're doing.
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
  using System.Collections.Immutable;
  using System.Linq;
#endif

  public class Set<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }
    public static readonly Set<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }
      return new Set<T>(d.ToImmutable(), containsNull);
    }
    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }
    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }
        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }
#else
    readonly HashSet<T> setImpl;
    Set(HashSet<T> s) {
      this.setImpl = s;
    }
    public static readonly Set<T> Empty = new Set<T>(new HashSet<T>());
    public static Set<T> FromElements(params T[] values) {
      return FromCollection(values);
    }
    public static Set<T> FromCollection(IEnumerable<T> values) {
      var s = new HashSet<T>(values);
      return new Set<T>(s);
    }
    public static Set<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var s = new HashSet<T>(values);
      s.Add(oneMoreValue);
      return new Set<T>(s);
    }
    public int Count {
      get { return this.setImpl.Count; }
    }
    public long LongCount {
      get { return this.setImpl.Count; }
    }
    public IEnumerable<T> Elements {
      get {
        return this.setImpl;
      }
    }
#endif

    public static Set<T> _DafnyDefaultValue() {
      return Empty;
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<Set<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
#else
        var s = new HashSet<T>();
#endif
        while (true) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }
#else
          yield return new Set<T>(new HashSet<T>(s));
#endif
          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }
          if (i == n) {
            // we have cycled through all the subsets
            break;
          }
          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }
    public bool Equals(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return containsNull == other.containsNull && this.setImpl.SetEquals(other.setImpl);
#else
      return this.setImpl.Count == other.setImpl.Count && IsSubsetOf(other);
#endif
    }
    public override bool Equals(object other) {
      return other is Set<T> && Equals((Set<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }
#endif
      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t)+3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
#endif
      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(Set<T> other) {
      return this.Count < other.Count && IsSubsetOf(other);
    }
    public bool IsSubsetOf(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && !other.containsNull) {
        return false;
      }
#endif
      if (other.setImpl.Count < this.setImpl.Count)
        return false;
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(Set<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(Set<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(Set<T> other) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      if (this.containsNull && other.containsNull) {
        return false;
      }
      ImmutableHashSet<T> a, b;
#else
      HashSet<T> a, b;
#endif
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      foreach (T t in a) {
        if (b.Contains(t))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G t) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
#else
      return (t == null || t is T) && this.setImpl.Contains((T)(object)t);
#endif
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Set<T> Union(Set<T> other) {
      return new Set<T>(this.setImpl.Union(other.setImpl), containsNull || other.containsNull);
    }
    public Set<T> Intersect(Set<T> other) {
      return new Set<T>(this.setImpl.Intersect(other.setImpl), containsNull && other.containsNull);
    }
    public Set<T> Difference(Set<T> other) {
        return new Set<T>(this.setImpl.Except(other.setImpl), containsNull && !other.containsNull);
    }
#else
    public Set<T> Union(Set<T> other) {
      if (this.setImpl.Count == 0)
        return other;
      else if (other.setImpl.Count == 0)
        return this;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in b)
        r.Add(t);
      foreach (T t in a)
        r.Add(t);
      return new Set<T>(r);
    }
    public Set<T> Intersect(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return other;
      HashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      var r = new HashSet<T>();
      foreach (T t in a) {
        if (b.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
    public Set<T> Difference(Set<T> other) {
      if (this.setImpl.Count == 0)
        return this;
      else if (other.setImpl.Count == 0)
        return this;
      var r = new HashSet<T>();
      foreach (T t in this.setImpl) {
        if (!other.setImpl.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
#endif
  }

  public class MultiSet<T>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<T, int> dict;
#else
    readonly Dictionary<T, int> dict;
#endif
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    MultiSet(ImmutableDictionary<T, int>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, int>.Empty.ToBuilder(), BigInteger.Zero);
#else
    MultiSet(Dictionary<T, int> d, BigInteger occurrencesOfNull) {
      this.dict = d;
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static MultiSet<T> Empty = new MultiSet<T>(new Dictionary<T, int>(0), BigInteger.Zero);
#endif
    public static MultiSet<T> FromElements(params T[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>(values.Length);
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromCollection(ICollection<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSeq(Sequence<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          var i = 0;
          if (!d.TryGetValue(t, out i)) {
            i = 0;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(Set<T> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var d = new Dictionary<T, int>();
#endif
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = 1;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }

    public static MultiSet<T> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(MultiSet<T> other) {
      return other.IsSubsetOf(this) && this.IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is MultiSet<T> && Equals((MultiSet<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (int i = 0; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(MultiSet<T> other) {
      return !Equals(other) && IsSubsetOf(other);
    }
    public bool IsSubsetOf(MultiSet<T> other) {
      if (other.occurrencesOfNull < this.occurrencesOfNull) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t) || other.dict[t] < dict[t])
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(MultiSet<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(MultiSet<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(MultiSet<T> other) {
      if (occurrencesOfNull > 0 && other.occurrencesOfNull > 0) {
        return false;
      }
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t))
          return false;
      }
      foreach (T t in other.dict.Keys) {
        if (dict.ContainsKey(t))
          return false;
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return t == null ? occurrencesOfNull > 0 : t is T && dict.ContainsKey((T)(object)t);
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      } else if (t is T && dict.ContainsKey((T)(object)t)) {
        return dict[(T)(object)t];
      } else {
        return BigInteger.Zero;
      }
    }
    public MultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var r = dict.ToBuilder();
#else
        var r = dict;
#endif
        return new MultiSet<T>(r, i);
      } else {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
        var r = dict.ToBuilder();
#else
        var r = new Dictionary<T, int>(dict);
#endif
        r[(T)(object)t] = (int)i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public MultiSet<T> Union(MultiSet<T> other) {
      if (dict.Count + occurrencesOfNull == 0)
        return other;
      else if (other.dict.Count + other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + dict[t];
      }
      foreach (T t in other.dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + other.dict[t];
      }
      return new MultiSet<T>(r, occurrencesOfNull + other.occurrencesOfNull);
    }
    public MultiSet<T> Intersect(MultiSet<T> other) {
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return other;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t)) {
          r.Add(t, other.dict[t] < dict[t] ? other.dict[t] : dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? other.occurrencesOfNull : occurrencesOfNull);
    }
    public MultiSet<T> Difference(MultiSet<T> other) { // \result == this - other
      if (dict.Count == 0 && occurrencesOfNull == 0)
        return this;
      else if (other.dict.Count == 0 && other.occurrencesOfNull == 0)
        return this;
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
#else
      var r = new Dictionary<T, int>();
#endif
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t)) {
          r.Add(t, dict[t]);
        } else if (other.dict[t] < dict[t]) {
          r.Add(t, dict[t] - other.dict[t]);
        }
      }
      return new MultiSet<T>(r, other.occurrencesOfNull < occurrencesOfNull ? occurrencesOfNull - other.occurrencesOfNull : BigInteger.Zero);
    }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (int i = 0; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var item in dict) {
          yield return item.Key;
        }
      }
    }
  }

  public class Map<U, V>
  {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    readonly ImmutableDictionary<U, V> dict;
#else
    readonly Dictionary<U, V> dict;
#endif
    readonly bool hasNullValue;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullValue", the value that "null" maps to

#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    Map(ImmutableDictionary<U, V>.Builder d, bool hasNullValue, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));
#else
    Map(Dictionary<U, V> d, bool hasNullValue, V nullValue) {
      this.dict = d;
      this.hasNullValue = hasNullValue;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(new Dictionary<U, V>(), false, default(V));
#endif

    public static Map<U, V> FromElements(params Pair<U, V>[] values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      var d = new Dictionary<U, V>(values.Length);
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public static Map<U, V> FromCollection(List<Pair<U, V>> values) {
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
#else
      var d = new Dictionary<U, V>(values.Count);
#endif
      var hasNullValue = false;
      var nullValue = default(V);
      foreach (Pair<U, V> p in values) {
        if (p.Car == null) {
          hasNullValue = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullValue, nullValue);
    }
    public int Count {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullValue ? 1 : 0); }
    }
    public static Map<U, V> _DafnyDefaultValue() {
      return Empty;
    }

    public bool Equals(Map<U, V> other) {
      if (hasNullValue != other.hasNullValue || dict.Count != other.dict.Count) {
        return false;
      } else if (hasNullValue && !Dafny.Helpers.AreEqual(nullValue, other.nullValue)) {
        return false;
      }
      foreach (U u in dict.Keys) {
        V v1 = dict[u];
        V v2;
        if (!other.dict.TryGetValue(u, out v2)) {
          return false; // other dictionary does not contain this element
        }
        if (!Dafny.Helpers.AreEqual(v1, v2)) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      return other is Map<U, V> && Equals((Map<U, V>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullValue) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullValue) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool IsDisjointFrom(Map<U, V> other) {
      if (hasNullValue && other.hasNullValue) {
        return false;
      }
      foreach (U u in dict.Keys) {
        if (other.dict.ContainsKey(u))
          return false;
      }
      foreach (U u in other.dict.Keys) {
        if (dict.ContainsKey(u))
          return false;
      }
      return true;
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullValue : u is U && dict.ContainsKey((U)(object)u);
    }
    public V Select(U index) {
      // evidently, the following will throw some exception if "index" in not a key of the map
      return index == null && hasNullValue ? nullValue : dict[index];
    }
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
    public Map<U, V> Update(U index, V val) {
      var d = dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#else
    public Map<U, V> Update(U index, V val) {
      if (index == null) {
        return new Map<U, V>(dict, true, val);
      } else {
        var d = new Dictionary<U, V>(dict);
        d[index] = val;
        return new Map<U, V>(d, hasNullValue, nullValue);
      }
    }
#endif
    public Set<U> Keys {
      get {
        if (hasNullValue) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public Set<V> Values {
      get {
        if (hasNullValue) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }
    public Set<_System.Tuple2<U, V>> Items {
      get {
        HashSet<_System.Tuple2<U, V>> result = new HashSet<_System.Tuple2<U, V>>();
        if (hasNullValue) {
          result.Add(_System.Tuple2<U, V>.create(default(U), nullValue));
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          result.Add(_System.Tuple2<U, V>.create(kvp.Key, kvp.Value));
        }
        return Dafny.Set<_System.Tuple2<U, V>>.FromCollection(result);
      }
    }
  }

  public class Sequence<T>
  {
    readonly T[] elmts;
    public Sequence(T[] ee) {
      elmts = ee;
    }
    public static Sequence<T> Empty {
      get {
        return new Sequence<T>(new T[0]);
      }
    }
    public static Sequence<T> FromElements(params T[] values) {
      return new Sequence<T>(values);
    }
    public static Sequence<char> FromString(string s) {
      return new Sequence<char>(s.ToCharArray());
    }
    public static Sequence<T> _DafnyDefaultValue() {
      return Empty;
    }
    public int Count {
      get { return elmts.Length; }
    }
    public long LongCount {
      get { return elmts.LongLength; }
    }
    public T[] Elements {
      get {
        return elmts;
      }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromElements(elmts);
        return st.Elements;
      }
    }
    public T Select(ulong index) {
      return elmts[index];
    }
    public T Select(long index) {
      return elmts[index];
    }
    public T Select(uint index) {
      return elmts[index];
    }
    public T Select(int index) {
      return elmts[index];
    }
    public T Select(BigInteger index) {
      return elmts[(int)index];
    }
    public Sequence<T> Update(long index, T t) {
      T[] a = (T[])elmts.Clone();
      a[index] = t;
      return new Sequence<T>(a);
    }
    public Sequence<T> Update(ulong index, T t) {
      return Update((long)index, t);
    }
    public Sequence<T> Update(BigInteger index, T t) {
      return Update((long)index, t);
    }
    public bool Equals(Sequence<T> other) {
      int n = elmts.Length;
      return n == other.elmts.Length && EqualUntil(other, n);
    }
    public override bool Equals(object other) {
      return other is Sequence<T> && Equals((Sequence<T>)other);
    }
    public override int GetHashCode() {
      if (elmts == null || elmts.Length == 0)
        return 0;
      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (elmts is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + Dafny.Helpers.ToString(t);
          sep = ", ";
        }
        return s + "]";
      }
    }
    bool EqualUntil(Sequence<T> other, int n) {
      for (int i = 0; i < n; i++) {
        if (!Dafny.Helpers.AreEqual(elmts[i], other.elmts[i]))
          return false;
      }
      return true;
    }
    public bool IsProperPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n < other.elmts.Length && EqualUntil(other, n);
    }
    public bool IsPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n <= other.elmts.Length && EqualUntil(other, n);
    }
    public Sequence<T> Concat(Sequence<T> other) {
      if (elmts.Length == 0)
        return other;
      else if (other.elmts.Length == 0)
        return this;
      T[] a = new T[elmts.Length + other.elmts.Length];
      System.Array.Copy(elmts, 0, a, 0, elmts.Length);
      System.Array.Copy(other.elmts, 0, a, elmts.Length, other.elmts.Length);
      return new Sequence<T>(a);
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        int n = elmts.Length;
        for (int i = 0; i < n; i++) {
          if (Dafny.Helpers.AreEqual(t, elmts[i]))
            return true;
        }
      }
      return false;
    }
    public Sequence<T> Take(long m) {
      if (elmts.LongLength == m)
        return this;
      T[] a = new T[m];
      System.Array.Copy(elmts, a, m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public Sequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public Sequence<T> Drop(long m) {
      if (m == 0)
        return this;
      T[] a = new T[elmts.Length - m];
      System.Array.Copy(elmts, m, a, 0, elmts.Length - m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public Sequence<T> Drop(BigInteger n) {
      if (n.IsZero)
        return this;
      return Drop((long)n);
    }
  }
  public struct Pair<A, B>
  {
    public readonly A Car;
    public readonly B Cdr;
    public Pair(A a, B b) {
      this.Car = a;
      this.Cdr = b;
    }
  }
  public partial class Helpers {
    public static bool AreEqual<G>(G a, G b) {
      return a == null ? b == null : a.Equals(b);
    }
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }
    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }
    public static G Default<G>() {
      System.Type ty = typeof(G);
      System.Reflection.MethodInfo mInfo = ty.GetMethod("_DafnyDefaultValue");
      if (mInfo != null) {
        G g = (G)mInfo.Invoke(null, null);
        return g;
      } else {
        return default(G);
      }
    }
    // Computing forall/exists quantifiers
    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1);; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true; ) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }
    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new Sequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it it possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u)
    {
      return u;
    }

    public static U Let<T, U>(T t, Func<T,U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational
  {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)
    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }
}

namespace @_System
{
  public class Tuple2<T0,T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.@Tuple2<T0,T1>;
      return oth != null && Dafny.Helpers.AreEqual(this._0, oth._0) && Dafny.Helpers.AreEqual(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    static Tuple2<T0,T1> theDefault;
    public static Tuple2<T0,T1> Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.@Tuple2<T0,T1>(Dafny.Helpers.Default<T0>(), Dafny.Helpers.Default<T1>());
        }
        return theDefault;
      }
    }
    public static Tuple2<T0,T1> _DafnyDefaultValue() { return Default; }
    public static Tuple2<T0,T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0,T1>(_0, _1);
    }
    public bool is____hMake3 { get { return true; } }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++)
        a[i0] = z;
      return a;
    }
  }
} // end of namespace Dafny
namespace _System {


  public partial class nat {
  }








  public class Tuple0 {
    public Tuple0() {
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    static Tuple0 theDefault;
    public static Tuple0 Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.Tuple0();
        }
        return theDefault;
      }
    }
    public static Tuple0 _DafnyDefaultValue() { return Default; }
    public static Tuple0 create() {
      return new Tuple0();
    }
    public bool is____hMake0 { get { return true; } }
    public static System.Collections.Generic.IEnumerable<Tuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }
} // end of namespace _System
namespace _0_Array_Compile {

  public partial class __default {
    public static Dafny.Set<A> elems<A>(A[] l) {
      return ((System.Func<Dafny.Set<A>>)(() => {
        var _coll0 = new System.Collections.Generic.List<A>();
        foreach (var _compr_0 in (Dafny.Helpers.SeqFromArray(l)).Elements) { A _122_x = (A)_compr_0;
          if ((Dafny.Helpers.SeqFromArray(l)).Contains(_122_x)) {
            _coll0.Add(_122_x);
          }
        }
        return Dafny.Set<A>.FromCollection(_coll0);
      }))();
    }
    public static Dafny.MultiSet<A> melems<A>(A[] l) {
      return Dafny.MultiSet<A>.FromSeq(Dafny.Helpers.SeqFromArray(l));
    }
  }
} // end of namespace _0_Array_Compile
namespace _1_Seq_Compile {

} // end of namespace _1_Seq_Compile
namespace _module {

  public partial class __default {
    public static void ScanArray(BigInteger n, out BigInteger[] v)
    {
    TAIL_CALL_START: ;
      v = new BigInteger[0];
      var _nw0 = new BigInteger[(int)(n)];
      v = _nw0;
      BigInteger _123_i;
      _123_i = new BigInteger(0);
      while ((_123_i) < (n)) {
        BigInteger _out0;
        __default.Scan(out _out0);
        (v)[(int)((_123_i))] = _out0;
        _123_i = (_123_i) + (new BigInteger(1));
      }
    }
    public static void Main()
    {
    TAIL_CALL_START: ;
      while (true) {
        BigInteger _124_n;
        BigInteger _out1;
        __default.Scan(out _out1);
        _124_n = _out1;
        if ((_124_n) == (new BigInteger(0))) {
          goto after_0;
        } else {
          BigInteger[] _125_v;
          BigInteger[] _out2;
          __default.ScanArray(_124_n, out _out2);
          _125_v = _out2;
          Stack1 _126_neg;
          var _nw1 = new Stack1();
          _nw1.__ctor();
          _126_neg = _nw1;
          Queue1 _127_pos;
          var _nw2 = new Queue1();
          _nw2.__ctor();
          _127_pos = _nw2;
          __default.reordenandoLaCola(_126_neg, _127_pos, _125_v);
          BigInteger _128_i;
          _128_i = new BigInteger(0);
          while ((_128_i) < (_124_n)) {
            Dafny.Helpers.Print((_125_v)[(int)(_128_i)]);
            if ((_128_i) != ((_124_n) - (new BigInteger(1)))) {
              Dafny.Helpers.Print(Dafny.Sequence<char>.FromString(" "));
            }
            _128_i = (_128_i) + (new BigInteger(1));
          }
          Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
        }
      }
    after_0: ;
    }
    public static void split(BigInteger[] v, Stack neg, Queue pos)
    {
    TAIL_CALL_START: ;
      BigInteger _129_i;
      _129_i = new BigInteger(0);
      while ((_129_i) < (new BigInteger((v).Length))) {
        { }
        { }
        if (((v)[(int)(_129_i)]) < (new BigInteger(0))) {
          { }
          (neg).Push((v)[(int)(_129_i)]);
        } else {
          { }
          (pos).Enqueue((v)[(int)(_129_i)]);
        }
        _129_i = (_129_i) + (new BigInteger(1));
      }
      { }
    }
    public static void FillFromStack(BigInteger[] r, BigInteger i, Stack st, out BigInteger l)
    {
    TAIL_CALL_START: ;
      l = BigInteger.Zero;
      l = new BigInteger(0);
      while (!((st).Empty())) {
        BigInteger _130_x;
        BigInteger _out3;
        (st).Pop(out _out3);
        _130_x = _out3;
        var _index0 = (i) + (l);
        (r)[(int)(_index0)] = _130_x;
        l = (l) + (new BigInteger(1));
      }
      l = (l) + (i);
    }
    public static void FillFromQueue(BigInteger[] r, BigInteger i, Queue q, out BigInteger l)
    {
    TAIL_CALL_START: ;
      l = BigInteger.Zero;
      l = new BigInteger(0);
      while (!((q).Empty())) {
        BigInteger _131_x;
        BigInteger _out4;
        (q).Dequeue(out _out4);
        _131_x = _out4;
        var _index1 = (i) + (l);
        (r)[(int)(_index1)] = _131_x;
        l = (l) + (new BigInteger(1));
      }
      l = (l) + (i);
    }
    public static void reordenandoLaCola(Stack neg, Queue pos, BigInteger[] v)
    {
      __default.split(v, neg, pos);
      { }
      { }
      { }
      BigInteger _132_i;
      _132_i = new BigInteger(0);
      BigInteger _out5;
      __default.FillFromStack(v, _132_i, neg, out _out5);
      _132_i = _out5;
      BigInteger _out6;
      __default.FillFromQueue(v, _132_i, pos, out _out6);
      _132_i = _out6;
      { }
    }
    public static void EvalPostfix(Dafny.Sequence<char> s, out BigInteger res)
    {
    TAIL_CALL_START: ;
      res = BigInteger.Zero;
      Stack _133_st;
      var _nw3 = new Stack1();
      _nw3.__ctor();
      _133_st = _nw3;
      BigInteger _134_i;
      _134_i = new BigInteger(0);
      while ((_134_i) < (new BigInteger((s).Count))) {
        char _135_c;
        _135_c = (s).Select(new BigInteger(0));
        if ((Dafny.Sequence<char>.FromString("0123456789")).Contains(_135_c)) {
          (_133_st).Push((new BigInteger(_135_c)) - (new BigInteger(48)));
        } else {
          if ((_133_st).Empty()) {
            res = (new BigInteger(0)) - (new BigInteger(1));
            return;
          }
          BigInteger _136_x;
          BigInteger _out7;
          (_133_st).Pop(out _out7);
          _136_x = _out7;
          if ((_133_st).Empty()) {
            res = (new BigInteger(0)) - (new BigInteger(1));
            return;
          }
          BigInteger _137_y;
          BigInteger _out8;
          (_133_st).Pop(out _out8);
          _137_y = _out8;
          BigInteger _138_n = BigInteger.Zero;
          if ((_135_c) == ('+')) {
            _138_n = (_136_x) + (_137_y);
          } else if ((_135_c) == ('-')) {
            _138_n = (_136_x) - (_137_y);
          } else if ((_135_c) == ('*')) {
            _138_n = (_136_x) * (_137_y);
          } else if ((_135_c) == ('/')) {
            if ((_137_y) == (new BigInteger(0))) {
              res = (new BigInteger(0)) - (new BigInteger(1));
              return;
            }
            { }
            _138_n = Dafny.Helpers.EuclideanDivision(_136_x, _137_y);
          }
          (_133_st).Push(_138_n);
        }
        _134_i = (_134_i) + (new BigInteger(1));
      }
      if ((_133_st).Empty()) {
        res = (new BigInteger(0)) - (new BigInteger(1));
        return;
      }
      { }
      BigInteger _out9;
      (_133_st).Top(out _out9);
      res = _out9;
    }
    public static char OpeningBrace(char c) {
      if ((c) == (')')) {
        return '(';
      } else  {
        if ((c) == (']')) {
          return '[';
        } else  {
          return '{';
        }
      }
    }
    public static void BalancedTest(Dafny.Sequence<char> s, out bool b)
    {
    TAIL_CALL_START: ;
      b = false;
      Stack _139_st;
      var _nw4 = new Stack1();
      _nw4.__ctor();
      _139_st = _nw4;
      BigInteger _140_i;
      _140_i = new BigInteger(0);
      while ((_140_i) < (new BigInteger((s).Count))) {
        if (((((s).Select(_140_i)) == ('(')) || (((s).Select(_140_i)) == ('['))) || (((s).Select(_140_i)) == ('{'))) {
          (_139_st).Push(new BigInteger((s).Select(_140_i)));
        } else if (((((s).Select(_140_i)) == (')')) || (((s).Select(_140_i)) == (']'))) || (((s).Select(_140_i)) == ('}'))) {
          if ((_139_st).Empty()) {
            b = false;
            return;
          } else {
            BigInteger _141_c;
            BigInteger _out10;
            (_139_st).Pop(out _out10);
            _141_c = _out10;
            if ((_141_c) != (new BigInteger(__default.OpeningBrace((s).Select(_140_i))))) {
              b = false;
              return;
            }
          }
        }
        _140_i = (_140_i) + (new BigInteger(1));
      }
      b = (_139_st).Empty();
      return;
    }
    public static void Print(Stack st)
    {
    TAIL_CALL_START: ;
      while (!((st).Empty())) {
        BigInteger _142_x;
        BigInteger _out11;
        (st).Pop(out _out11);
        _142_x = _out11;
        Dafny.Helpers.Print(_142_x);
        Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
      }
    }
    public static Dafny.Set<A> BigUnion<A>(Dafny.Set<Dafny.Set<A>> S) {
      return ((System.Func<Dafny.Set<A>>)(() => {
        var _coll1 = new System.Collections.Generic.List<A>();
        foreach (var _compr_1 in (S).Elements) { Dafny.Set<A> _143_X = (Dafny.Set<A>)_compr_1;
          foreach (var _compr_2 in (_143_X).Elements) { A _144_x = (A)_compr_2;
            if (((S).Contains(_143_X)) && ((_143_X).Contains(_144_x))) {
              _coll1.Add(_144_x);
            }
          }
        }
        return Dafny.Set<A>.FromCollection(_coll1);
      }))();
    }
    public static BigInteger abs(BigInteger x) {
      if ((x) < (new BigInteger(0))) {
        return (new BigInteger(0)) - (x);
      } else  {
        return x;
      }
    }
  }

  public partial class Stack1 : Stack {
    public List<BigInteger> list = default(List<BigInteger>);
    public void __ctor()
    {
      var _this = this;
    TAIL_CALL_START: ;
      var _nw5 = new List<BigInteger>();
      _nw5.__ctor();
      (_this).list = _nw5;
    }
    public bool Empty() {
      return (this.list.head) == (object) ((SNode<BigInteger>)null);
    }
    public void Top(out BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      x = BigInteger.Zero;
      x = _this.list.head.data;
    }
    public void Push(BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this.list).Push(x);
    }
    public void Pop(out BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      x = BigInteger.Zero;
      BigInteger _out12;
      (_this.list).Pop(out _out12);
      x = _out12;
    }
  }

  public partial class Queue1 : Queue {
    public DoublyLinkedListWithLast list = default(DoublyLinkedListWithLast);
    public bool Empty() {
      return (this.list.list.head) == (object) ((DNode)null);
    }
    public void __ctor()
    {
      var _this = this;
    TAIL_CALL_START: ;
      var _nw6 = new DoublyLinkedListWithLast();
      _nw6.__ctor();
      (_this).list = _nw6;
    }
    public void Front(out BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      x = BigInteger.Zero;
      BigInteger _out13;
      (_this.list).Front(out _out13);
      x = _out13;
    }
    public void Enqueue(BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this.list).PushBack(x);
    }
    public void Dequeue(out BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      x = BigInteger.Zero;
      BigInteger _out14;
      (_this.list).PopFront(out _out14);
      x = _out14;
    }
  }

  public partial class QueueIterator {
    public DNode node = (DNode)null;
    public void __ctor(Queue1 l)
    {
      var _this = this;
    TAIL_CALL_START: ;
      { }
      { }
      (_this).node = l.list.list.head;
    }
    public bool HasNext() {
      return (this.node) != (object) ((DNode)null);
    }
    public void Next(out BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      x = BigInteger.Zero;
      { }
      x = _this.node.data;
      { }
      (_this).node = _this.node.next;
    }
  }



  public interface Stack {
    bool Empty();
    void Top(out BigInteger x);
    void Push(BigInteger x);
    void Pop(out BigInteger x);
  }
  public class _Companion_Stack {
  }

  public interface Queue {
    bool Empty();
    void Front(out BigInteger x);
    void Enqueue(BigInteger x);
    void Dequeue(out BigInteger x);
  }
  public class _Companion_Queue {
  }

  public partial class SNode<A> {
    public A data = Dafny.Helpers.Default<A>();
    public SNode<A> next = (SNode<A>)null;
    public void __ctor(A data, SNode<A> next)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).data = data;
      (_this).next = next;
    }
  }

  public partial class List<A> {
    public SNode<A> head = (SNode<A>)null;
    public void __ctor()
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).head = (SNode<A>)null;
      { }
    }
    public void PopNode(out SNode<A> h)
    {
      var _this = this;
    TAIL_CALL_START: ;
      h = default(SNode<A>);
      h = _this.head;
      { }
      (_this).head = _this.head.next;
      { }
      { }
      { }
      { }
    }
    public void Pop(out A res)
    {
      var _this = this;
    TAIL_CALL_START: ;
      res = Dafny.Helpers.Default<A>();
      SNode<A> _145_tmp;
      SNode<A> _out15;
      (_this).PopNode(out _out15);
      _145_tmp = _out15;
      res = _145_tmp.data;
    }
    public void PushNode(SNode<A> h)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (h).next = _this.head;
      (_this).head = h;
      { }
      { }
    }
    public void Push(A x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      SNode<A> _146_n;
      var _nw7 = new SNode<A>();
      _nw7.__ctor(x, (SNode<A>)null);
      _146_n = _nw7;
      (_this).PushNode(_146_n);
    }
    public void Append(List<A> other)
    {
      if ((this.head) == (object) ((SNode<A>)null)) {
        (this).head = other.head;
        { }
      } else {
        SNode<A> _147_last;
        _147_last = this.head;
        { }
        while ((_147_last.next) != (object) ((SNode<A>)null)) {
          _147_last = _147_last.next;
          { }
        }
        { }
        (_147_last).next = other.head;
        { }
        { }
      }
      (other).head = (SNode<A>)null;
      { }
    }
    public void PopPush(List<A> other)
    {
      var _this = this;
    TAIL_CALL_START: ;
      SNode<A> _148_n;
      SNode<A> _out16;
      (_this).PopNode(out _out16);
      _148_n = _out16;
      (other).PushNode(_148_n);
    }
    public void Reverse()
    {
      var _this = this;
    TAIL_CALL_START: ;
      List<A> _149_aux;
      var _nw8 = new List<A>();
      _nw8.__ctor();
      _149_aux = _nw8;
      (_149_aux).head = _this.head;
      { }
      (_this).head = (SNode<A>)null;
      { }
      while ((_149_aux.head) != (object) ((SNode<A>)null)) {
        (_149_aux).PopPush(_this);
      }
    }
    public void Insert(SNode<A> mid, A x)
    {
      { }
      SNode<A> _150_n;
      var _nw9 = new SNode<A>();
      _nw9.__ctor(x, mid.next);
      _150_n = _nw9;
      (mid).next = _150_n;
      {
        { }
        { }
        { }
        { }
      }
    }
    public void RemoveNext(SNode<A> mid)
    {
      { }
      { }
      { }
      { }
      (mid).next = mid.next.next;
      { }
    }
    public void FindPrev(SNode<A> mid, out SNode<A> prev)
    {
      prev = default(SNode<A>);
      prev = this.head;
      { }
      while ((prev.next) != (object) (mid)) {
        { }
        prev = prev.next;
        { }
      }
    }
  }

  public partial class DoublyLinkedListWithLast {
    public DoublyLinkedList list = default(DoublyLinkedList);
    public DNode last = (DNode)null;
    public void __ctor()
    {
      var _this = this;
    TAIL_CALL_START: ;
      var _nw10 = new DoublyLinkedList();
      _nw10.__ctor();
      (_this).list = _nw10;
      (_this).last = (DNode)null;
    }
    public void Front(out BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      x = BigInteger.Zero;
      x = _this.list.head.data;
    }
    public void Back(out BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      x = BigInteger.Zero;
      { }
      { }
      x = _this.last.data;
    }
    public void PushFront(BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      DNode _151_ohead;
      _151_ohead = _this.list.head;
      { }
      (_this.list).PushFront(x);
      if ((_151_ohead) == (object) ((DNode)null)) {
        (_this).last = _this.list.head;
      }
    }
    public void PopFront(out BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      x = BigInteger.Zero;
      { }
      if ((_this.list.head) == (object) (_this.last)) {
        (_this).last = (DNode)null;
      }
      { }
      BigInteger _out17;
      (_this.list).PopFront(out _out17);
      x = _out17;
    }
    public void PushBack(BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      if ((_this.last) == (object) ((DNode)null)) {
        { }
        (_this.list).PushFront(x);
        (_this).last = _this.list.head;
      } else {
        { }
        (_this.list).Insert(_this.last, x);
        (_this).last = _this.last.next;
        { }
        { }
      }
    }
    public void PopBack(out BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      x = BigInteger.Zero;
      if ((_this.list.head) == (object) (_this.last)) {
        { }
        { }
        { }
        { }
        x = _this.list.head.data;
        var _obj0 = _this.list;
        _obj0.head = (DNode)null;
        { }
        (_this).last = (DNode)null;
        { }
        { }
        { }
      } else {
        x = _this.last.data;
        DNode _152_prev;
        _152_prev = _this.last.prev;
        { }
        (_this.list).RemoveNext(_152_prev);
        (_this).last = _152_prev;
      }
    }
  }


  public partial class DNode {
    public DNode prev = (DNode)null;
    public BigInteger data = BigInteger.Zero;
    public DNode next = (DNode)null;
    public void __ctor(DNode prev, BigInteger data, DNode next)
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).prev = prev;
      (_this).data = data;
      (_this).next = next;
    }
  }

  public partial class DoublyLinkedList {
    public DNode head = (DNode)null;
    public void __ctor()
    {
      var _this = this;
    TAIL_CALL_START: ;
      (_this).head = (DNode)null;
      { }
    }
    public void PopFront(out BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      x = BigInteger.Zero;
      { }
      { }
      { }
      x = _this.head.data;
      (_this).head = _this.head.next;
      { }
      if ((_this.head) != (object) ((DNode)null)) {
        var _obj1 = _this.head;
        _obj1.prev = (DNode)null;
      }
    }
    public void PushFront(BigInteger x)
    {
      var _this = this;
    TAIL_CALL_START: ;
      DNode _153_n;
      var _nw11 = new DNode();
      _nw11.__ctor((DNode)null, x, _this.head);
      _153_n = _nw11;
      if ((_this.head) != (object) ((DNode)null)) {
        var _obj2 = _this.head;
        _obj2.prev = _153_n;
      }
      (_this).head = _153_n;
      { }
      { }
    }
    public void Insert(DNode mid, BigInteger x)
    {
      { }
      DNode _154_n;
      var _nw12 = new DNode();
      _nw12.__ctor(mid, x, mid.next);
      _154_n = _nw12;
      { }
      { }
      { }
      if ((mid.next) != (object) ((DNode)null)) {
        { }
        { }
        var _obj3 = mid.next;
        _obj3.prev = _154_n;
      }
      (mid).next = _154_n;
      { }
    }
    public void RemoveNext(DNode mid)
    {
      { }
      { }
      { }
      { }
      (mid).next = mid.next.next;
      if ((mid.next) != (object) ((DNode)null)) {
        var _obj4 = mid.next;
        _obj4.prev = mid;
      }
      { }
    }
    public void FindPrev(DNode mid, out DNode prev)
    {
      prev = default(DNode);
      prev = this.head;
      { }
      while ((prev.next) != (object) (mid)) {
        { }
        prev = prev.next;
        { }
      }
    }
  }
} // end of namespace _module

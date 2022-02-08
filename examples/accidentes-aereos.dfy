include "../src/linear/layer1/Stack.dfy"

predicate AdjacentSummits(v: seq<nat>, i: nat, j: nat)
  requires 0 <= i < j < |v|
{
  && v[i] > v[j]
  && forall k | i < k < j :: v[i] > v[k] && v[j] >= v[k]
}

lemma NoSummitsInBetween(v: seq<nat>, i: nat, j: nat)
  requires 0 <= i < j < |v|
  requires AdjacentSummits(v, i, j)
  ensures forall k | i < k < j :: !AdjacentSummits(v, k, j)
{}

// This is trivial since there is no natural number less than 0
lemma FirstNoSummit(v: seq<nat>)
  requires |v| > 0
  ensures !exists i :: i < 0 && AdjacentSummits(v, i, 0)
{}

lemma UniqueSummits(v: seq<nat>, k: nat)
  requires 1 <= k < |v|
  ensures
    forall i, j
      | 0 <= i < k && 0 <= j < k
      && AdjacentSummits(v, i, k)
      && AdjacentSummits(v, j, k)
    :: i == j
{}

lemma TransitiveSeq(v: seq<int>)
  requires forall i | 0 <= i < |v|-1 :: v[i] > v[i+1]
  ensures forall i, j | 0 <= i < j < |v| :: v[i] > v[j]
{
  if v == [] {
  } else {
    TransitiveSeq(v[1..]);
    assert forall i, j | 1 <= i < j < |v| :: v[i] > v[j];
    assert |v| >= 2 ==> v[0] > v[1];
    assert forall i | 1 <= i < |v| :: v[0] > v[i];
  }
}

lemma TransitiveSeqSeq(v: seq<int>, idcs: seq<nat>)
  requires forall i | 0 <= i < |idcs| :: idcs[i] < |v|
  requires forall i | 0 <= i < |idcs|-1 :: v[idcs[i]] < v[idcs[i+1]]
  ensures forall i, j | 0 <= i < j < |idcs| :: v[idcs[i]] < v[idcs[j]]
{
  if idcs == [] {
  } else {
    TransitiveSeqSeq(v, idcs[1..]);
    assert forall i, j | 1 <= i < j < |idcs| :: v[idcs[i]] < v[idcs[j]];
    assert |idcs| >= 2 ==> v[idcs[0]] < v[idcs[1]];
    assert forall i | 1 <= i < |idcs| :: v[idcs[0]] < v[idcs[i]];
  }
}

method RemoveLess(st: Stack, v: array<nat>, i: nat) returns (ghost n: nat)
  modifies st, st.Repr()
  requires st.Valid()
  requires {v} !! {st} + st.Repr()
  requires forall x | x in st.Repr() :: allocated(x)

  requires i < v.Length
  requires forall j | 0 <= j < |st.Model()| :: 0 <= st.Model()[j] < i
  requires forall j | 0 <= j < |st.Model()|-1 :: st.Model()[j+1] < st.Model()[j]
  requires forall j | 0 <= j < |st.Model()|-1 :: AdjacentSummits(v[..], st.Model()[j+1], st.Model()[j])
  requires forall j | 0 <= j < |st.Model()|-1 :: v[st.Model()[j+1]] > v[st.Model()[j]]
  requires !st.Empty() ==> st.Top() == i-1

  ensures {v} !! {st} + st.Repr()
  ensures st.Valid()

  ensures n <= old(|st.Model()|)
  ensures forall j | j in old(st.Model()[..n]) :: v[j] <= v[i]
  ensures forall j | j in old(st.Model()[n..]) :: v[j] > v[i]
  ensures st.Model() == old(st.Model()[n..])
  ensures !st.Empty() ==> forall j | st.Top() < j < i :: v[j] <= v[i]

  requires forall x | x in st.Repr() :: allocated(x)
  ensures forall x {:trigger x in st.Repr(), x in old(st.Repr())} | x in st.Repr() && x !in old(st.Repr()) :: fresh(x)
  ensures fresh(st.Repr()-old(st.Repr()))
  ensures forall x | x in st.Repr() :: allocated(x)
{
  n := 0;
  while !st.Empty() && v[st.Top()] <= v[i]
    decreases old(|st.Model()|) - n
    invariant st.Valid()
    invariant {v} !! {st} + st.Repr()

    invariant n <= old(|st.Model()|)
    invariant st.Model() == old(st.Model()[n..])
    invariant forall j | 0 <= j < |st.Model()| :: 0 <= st.Model()[j] < i;
    invariant forall j | j in old(st.Model()[..n]) :: v[j] <= v[i]
    invariant forall j | 0 <= j < |st.Model()|-1 :: AdjacentSummits(v[..], st.Model()[j+1], st.Model()[j])
    invariant forall j | 0 <= j < |st.Model()|-1 :: st.Model()[j+1] < st.Model()[j]
    invariant forall j | 0 <= j < |st.Model()|-1 :: v[st.Model()[j+1]] > v[st.Model()[j]]
    invariant !st.Empty() ==> forall j | st.Top() < j < i :: v[j] < v[st.Top()] && v[j] <= v[i]

    invariant forall x {:trigger x in st.Repr(), x in old(st.Repr())} | x in st.Repr() && x !in old(st.Repr()) :: fresh(x)
    invariant fresh(st.Repr()-old(st.Repr()))
    invariant forall x | x in st.Repr() :: allocated(x)
  {
    var T := st.Pop();
    n := n + 1;
  }
  TransitiveSeqSeq(v[..], st.Model());
}

method FindSummits(v: array<nat>, st: Stack) returns (r: array<int>)
  modifies st, st.Repr()

  requires st.Valid() && st.Empty()

  ensures v.Length == r.Length
  ensures forall i | 0 <= i < r.Length :: -1 <= r[i] < i
  ensures forall i | 0 <= i < r.Length :: r[i] != -1 ==> AdjacentSummits(v[..], r[i], i)
  ensures forall i | 0 <= i < r.Length :: r[i] == -1 ==> forall j | 0 <= j < i :: !AdjacentSummits(v[..], j, i)

  requires {v} !! {st} + st.Repr()
  ensures {v} !! {st} + st.Repr()
  ensures {r} !! {st} + st.Repr()

  requires forall x | x in st.Repr() :: allocated(x)
  ensures forall x {:trigger x in st.Repr(), x in old(st.Repr())} | x in st.Repr() && x !in old(st.Repr()) :: fresh(x)
  ensures fresh(st.Repr()-old(st.Repr()))
  ensures forall x | x in st.Repr() :: allocated(x)
{
  r := new int[v.Length];
  var i := 0;
  if r.Length > 0 {
    st.Push(0);
    r[0] := -1;
    i := 1;
  } else {
    return;
  }
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant st.Valid()

    invariant !st.Empty()
    invariant st.Top() == i-1
    invariant forall j | 0 <= j < |st.Model()| :: 0 <= st.Model()[j] < i
    invariant forall j | 0 <= j < |st.Model()|-1 :: st.Model()[j+1] < st.Model()[j]
    invariant forall j | 0 <= j < |st.Model()|-1 :: AdjacentSummits(v[..], st.Model()[j+1], st.Model()[j])
    invariant forall j | 0 <= j < |st.Model()|-1 :: v[st.Model()[j+1]] > v[st.Model()[j]]
    invariant forall x | x in v[..i] :: v[st.Model()[|st.Model()|-1]] >= x
    invariant forall j | 0 <= j < i :: -1 <= r[j] < j
    invariant forall j | 0 <= j < i :: r[j] != -1 ==> AdjacentSummits(v[..], r[j], j)
    invariant forall j | 0 <= j < i :: r[j] == -1 ==> forall k | 0 <= k < j :: !AdjacentSummits(v[..], k, j)

    invariant {v} !! {st} + st.Repr()
    invariant {r} !! {st} + st.Repr()

    invariant forall x {:trigger x in st.Repr(), x in old(st.Repr())} | x in st.Repr() && x !in old(st.Repr()) :: fresh(x)
    invariant fresh(st.Repr()-old(st.Repr()))
    invariant forall x | x in st.Repr() :: allocated(x)
  {
    ghost var max := v[st.Model()[|st.Model()|-1]];
    ghost var k := RemoveLess(st, v, i);
    assert forall x | x in v[..i] :: max >= x;
    if st.Empty() {
      r[i] := -1;
      assert v[i] >= max;
      assert forall x | x in v[..i] :: v[i] >= x;
      assert forall j | 0 <= j < i :: v[j] in v[..i] && v[i] >= v[j];
      assert forall j | 0 <= j < i :: !AdjacentSummits(v[..], j, i);
    } else {
      r[i] := st.Top();
      assert st.Top() < i;
      assert v[st.Top()] > v[i];
      assert forall j | st.Top() < j < i :: v[i] >= v[j];
      assert AdjacentSummits(v[..], st.Top(), i);
    }
    st.Push(i);
    i := i + 1;
  }
}

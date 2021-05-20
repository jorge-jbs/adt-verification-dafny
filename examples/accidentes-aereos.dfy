include "../src/linear/adt/Stack.dfy"

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

lemma InductionStep(v: seq<nat>, i: nat, j: nat)
  requires i < j < |v|-1
  requires AdjacentSummits(v, i, j)
  ensures v[j] < v[j+1] && v[i] > v[j+1] ==> AdjacentSummits(v, i, j+1)
  ensures v[j] < v[j+1] && v[i] <= v[j+1] ==> !AdjacentSummits(v, i, j+1)
  ensures v[j] > v[j+1] ==> AdjacentSummits(v, j, j+1)
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

lemma TransitiveSeqSeq(v: seq<int>, is: seq<nat>)
  requires forall i | 0 <= i < |is| :: is[i] < |v|
  requires forall i | 0 <= i < |is|-1 :: v[is[i]] < v[is[i+1]]
  ensures forall i, j | 0 <= i < j < |is| :: v[is[i]] < v[is[j]]
{
  if is == [] {
  } else {
    TransitiveSeqSeq(v, is[1..]);
    assert forall i, j | 1 <= i < j < |is| :: v[is[i]] < v[is[j]];
    assert |is| >= 2 ==> v[is[0]] < v[is[1]];
    assert forall i | 1 <= i < |is| :: v[is[0]] < v[is[i]];
  }
}

method RemoveLess(st: Stack, v: array<nat>, i: nat) returns (n: nat)
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
  ensures forall x | x in st.Repr() - old(st.Repr()) :: fresh(x)
  ensures forall x | x in st.Repr() :: allocated(x)

  ensures n <= old(|st.Model()|)
  ensures forall j | j in old(st.Model()[..n]) :: v[j] <= v[i]
  ensures forall j | j in old(st.Model()[n..]) :: v[j] > v[i]
  ensures st.Model() == old(st.Model()[n..])
  ensures !st.Empty() ==> forall j | st.Top() < j < i :: v[j] <= v[i]
{
  n := 0;
  while !st.Empty() && v[st.Top()] <= v[i]
    decreases old(|st.Model()|) - n
    invariant st.Valid()
    invariant {v} !! {st} + st.Repr()
    invariant forall x | x in st.Repr() - old(st.Repr()) :: fresh(x)
    invariant forall x | x in st.Repr() :: allocated(x)

    invariant n <= old(|st.Model()|)
    invariant st.Model() == old(st.Model()[n..])
    invariant forall j | 0 <= j < |st.Model()| :: 0 <= st.Model()[j] < i;
    invariant forall j | j in old(st.Model()[..n]) :: v[j] <= v[i]
    invariant forall j | 0 <= j < |st.Model()|-1 :: AdjacentSummits(v[..], st.Model()[j+1], st.Model()[j])
    invariant forall j | 0 <= j < |st.Model()|-1 :: st.Model()[j+1] < st.Model()[j]
    invariant forall j | 0 <= j < |st.Model()|-1 :: v[st.Model()[j+1]] > v[st.Model()[j]]
    invariant !st.Empty() ==> forall j | st.Top() < j < i :: v[j] < v[st.Top()] && v[j] <= v[i]
  {
    var T := st.Pop();
    n := n + 1;
  }
  TransitiveSeqSeq(v[..], st.Model());
}

method FindSummits(v: array<nat>, st: Stack) returns (r: array<int>)
  modifies st, st.Repr()

  requires st.Valid() && st.Empty()
  requires {v} !! {st} + st.Repr()
  requires forall x | x in st.Repr() :: allocated(x)

  ensures v.Length == r.Length
  ensures forall i | 0 <= i < r.Length :: -1 <= r[i] < i
  ensures forall i | 0 <= i < r.Length :: r[i] != -1 ==> AdjacentSummits(v[..], r[i], i)
  ensures forall i | 0 <= i < r.Length :: r[i] == -1 ==> forall j | 0 <= j < i :: !AdjacentSummits(v[..], j, i)

  ensures forall x | x in st.Repr() - old(st.Repr()) :: fresh(x)
  ensures forall x | x in st.Repr() :: allocated(x)
  ensures {v} !! {st} + st.Repr()
  ensures {r} !! {st} + st.Repr()
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
    invariant {v} !! {st} + st.Repr()
    invariant {r} !! {st} + st.Repr()
    invariant forall x | x in st.Repr() - old(st.Repr()) :: fresh(x)
    invariant forall x | x in st.Repr() :: allocated(x)

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
  {
    ghost var max := v[st.Model()[|st.Model()|-1]];
    var k := RemoveLess(st, v, i);
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

predicate AdjacentSummits(v: seq<nat>, i: nat, j: nat)
  requires 0 <= i < j < |v|
{
  && v[i] > v[j]
  && forall k | i < k < j :: v[i] > v[k] && v[j] > v[k]
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

method FindSummits(v: array<nat>) returns (r: array<int>)
  ensures v.Length == r.Length
  ensures forall i | 0 <= i < r.Length :: -1 <= r[i] < i
  ensures forall i | 0 <= i < r.Length :: r[i] != -1 ==> AdjacentSummits(v[..], r[i], i)
  ensures forall i | 0 <= i < r.Length :: r[i] == -1 ==> forall j | 0 <= j < i :: !AdjacentSummits(v[..], j, i)

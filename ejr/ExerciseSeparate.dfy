predicate strictNegative(v : array<int>, i : int, j : int)
  reads v
  requires 0 <= i <=  j <= v.Length
{
  forall u | i <= u < j :: v[u] < 0
}

predicate positive(s : seq<int>)
{
  forall u :: 0 <= u < |s| ==> s[u] >= 0
}

predicate isPermutation(s : seq<int>, t : seq<int>)
{
  multiset(s) == multiset(t)
}

method separate(v : array<int>) returns (i : int)
  modifies v
  ensures 0 <= i <= v.Length
  ensures positive(v[0..i]) && strictNegative(v, i, v.Length)
  ensures isPermutation(v[0..v.Length], old(v[0..v.Length]))
{
  i := 0;
  var j := v.Length;
  while i < j
    invariant 0 <= i <= j <= v.Length
    invariant positive(v[0..i]) && strictNegative(v, j, v.Length)
    invariant isPermutation(v[0..v.Length], old(v[0..v.Length]))
  {
    if v[i] >= 0 {
      i := i + 1;
    } else if v[j - 1] < 0 {
      j := j - 1;
    } else {
      v[i], v[j-1] := v[j-1], v[i];
      i := i + 1;
      j := j - 1;
    }
  }
}

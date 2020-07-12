method mmaximum(v : array<int>) returns (i : int)
  requires v.Length > 0
  ensures 0 <= i < v.Length
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
{
  i := 0;
  var j := 0;
  while j < v.Length
    invariant 0 <= i < v.Length
    invariant 0 <= j <= v.Length
    invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
  {
    if v[i] < v[j] {
      i := j;
    }
    j := j + 1;
  }
}

//Algorithm 1: From left to right return the first
//Algorithm 2: From right to left return the last

method mfirstMaximum(v : array<int>) returns (i : int)
  requires v.Length>0
  ensures 0 <= i < v.Length
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
  ensures forall l :: 0 <= l < i ==> v[i] > v[l]
{
  i := 0;
  var j := 0;
  while j < v.Length
    invariant 0 <= i < v.Length
    invariant 0 <= j <= v.Length
    invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
    invariant forall l :: 0 <= l < i ==> v[i] > v[l]
  {
    if v[i] < v[j] {
      i := j;
    }
    j := j + 1;
  }
}
//Algorithm: from left to right

method mlastMaximum(v:array<int>) returns (i:int)
  requires v.Length>0
  ensures 0 <= i < v.Length
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
  ensures forall l :: i < l < v.Length ==> v[i] > v[l]
{
  i := v.Length - 1;
  var j := v.Length - 1;
  while j >= 0
    invariant 0 <= i < v.Length
    invariant -1 <= j < v.Length
    invariant forall k :: j < k < v.Length ==> v[i] >= v[k]
    invariant forall l :: i < l < v.Length ==> v[i] > v[l]
  {
    if v[i] < v[j] {
      i := j;
    }
    j := j - 1;
  }
}

//Algorithm : from left to right
//Algorithm : from right to left

method mmaxvalue(v:array<int>) returns (m:int)
  requires v.Length > 0
  ensures m in v[..]
  ensures forall k :: 0 <= k < v.Length ==> m >= v[k]
{
  m := v[0];
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant m in v[..]
    invariant forall k :: 0 <= k < i ==> m >= v[k]
  {
    if v[i] > m {
      m := v[i];
    }
    i := i + 1;
  }
}

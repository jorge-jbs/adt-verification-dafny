predicate positive(s : seq<int>)
{
  forall u :: 0 <= u < |s| ==> s[u] >= 0
}


predicate positiveA(a : array<int>, i : int)
  requires 0 <= i <= a.Length
  reads a;
{
  positive(a[0..i])
}




method mpositive1(v:array<int>) returns (b:bool)
  ensures b == positive(v[0..v.Length])
//ensures b==positiveA(v,v.Length)
{
  var i:int;
  b := true;
  i := 0;
  while i < v.Length && b
    invariant 0 <= i <= v.Length
    invariant b == positive(v[0..i])
    decreases v.Length - i
  {
    b := v[i] >= 0;
    i := i + 1;
  }
}

method mpositive2(v:array<int>) returns (b:bool)
  ensures b == positive(v[0..v.Length])
  //ensures b==positiveA(v,v.Length)
{
  var i : int;
  i := 0;
  while i < v.Length && v[i] >= 0
    invariant 0 <= i <= v.Length
    invariant positive(v[0..i])
    decreases v.Length - i
  {
    i := i + 1;
  }
  b := i == v.Length;
}

method mpositive3(v:array<int>) returns (b:bool)
  ensures b == positive(v[0..v.Length])
  //Now an algorithm from right to left
{
  var i := v.Length - 1;
  while i >= 0 && v[i] >= 0
    invariant -1 <= i < v.Length
    invariant positive(v[i+1..])
    decreases i
  {
    i := i - 1;
  }
  b := i == -1;
}

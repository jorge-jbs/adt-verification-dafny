predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}

//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
method mcontained(v : array<int>, w : array<int>, n : nat, m : nat)
  returns (b : bool)
  requires n <= v.Length
  requires m <= w.Length
  requires strictSorted(v[..])
  requires strictSorted(w[..])
  ensures b <==> forall i :: 0 <= i < n ==> v[i] in w[..m]
{
  var i := 0;
  var j := 0;
  while j < m && i < n
    invariant 0 <= i <= n
    invariant 0 <= j <= m
    invariant forall k :: 0 <= k < i ==> v[k] in w[..j]
    invariant i < v.Length ==> !(v[i] in w[..j])
  {
    j := j + 1;
    while i < n && v[i] == w[j-1]
      invariant 0 <= i <= n
      invariant 0 <= j <= m
      invariant forall k :: 0 <= k < i ==> v[k] in w[..j]
    {
      i := i + 1;
    }
  }
  if i >= n {
    b := true;
  } else {
    b := false;
  }
}

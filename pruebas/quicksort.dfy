
/*
method partition(n : nat, V : array<int>, pivot : int) returns (m : nat)
    modifies V
    requires V.Length == n
    ensures m <= n
    ensures forall k : nat :: 0 <= k < m ==> V[k] < pivot
    ensures forall k : nat :: m <= k < n ==> pivot <= V[k]
    //ensures forall i :: 0 <= i < n ==> exists j :: 0 <= j < n && old(V[i]) == V[j]
    ensures multiset(V[..]) == multiset(old(V)[..])
{
    var i := 0;
    var j := n;
    assert forall k : nat :: 0 <= k < 0 ==> V[k] < pivot;
    assert forall k : nat :: n <= k < n ==> pivot <= V[k];
    while i < j
        invariant i <= j <= n
        invariant forall k : nat :: 0 <= k < i ==> V[k] < pivot
        invariant forall k : nat :: j <= k < n ==> pivot <= V[k]
    {
        if V[i] < pivot {
            i := i + 1;
        } else {
            assert pivot <= V[i];
            V[i], V[j-1] := V[j-1], V[i];
            j := j - 1;
        }
        assert i <= j <= n;
        assert forall k : nat :: 0 <= k < i ==> V[k] < pivot;
        assert forall k : nat :: j <= k < n ==> pivot <= V[k];
    }
    assert i == j;
    assert i <= n &&
           forall k : nat :: 0 <= k < i ==> V[k] < pivot &&
           forall k : nat :: i <= k < n ==> pivot <= V[k];
    m := i;
    assert i <= n;
    assert forall k : nat :: 0 <= k < i ==> V[k] < pivot;
    assert forall k : nat :: i <= k < n ==> pivot <= V[k];
}
*/

method partition(l : nat, n : nat, V : array<int>, pivot : int) returns (m : nat)
    modifies V // should be V[l..n]
    requires 0 <= l <= n <= V.Length
    ensures m <= n
    ensures forall k : nat :: l <= k < m ==> V[k] < pivot
    ensures forall k : nat :: m <= k < n ==> pivot <= V[k]
    ensures forall a, b : nat :: l <= a < m <= b < n ==> V[a] <= V[b]
    //ensures pivot in multiset(V[..]) ==> l < m < n
    ensures multiset(V[..]) == multiset(old(V)[..])
    ensures forall k : nat :: (k < l || n <= k < V.Length) ==> old(V[k]) == V[k]
{
    var i := l;
    var j := n;
    assert forall k : nat :: l <= k < l ==> V[k] < pivot;
    assert forall k : nat :: n <= k < n ==> pivot <= V[k];
    while i < j
        invariant l <= i <= j <= n
        invariant forall k : nat :: l <= k < i ==> V[k] < pivot
        invariant forall k : nat :: j <= k < n ==> pivot <= V[k]
        invariant forall k : nat :: (k < l || n <= k < V.Length) ==> old(V[k]) == V[k]
    {
        if V[i] < pivot {
            i := i + 1;
        } else {
            assert pivot <= V[i];
            V[i], V[j-1] := V[j-1], V[i];
            j := j - 1;
        }
        assert i <= j <= n;
        assert forall k : nat :: l <= k < i ==> V[k] < pivot;
        assert forall k : nat :: j <= k < n ==> pivot <= V[k];
    }
    assert i == j;
    assert i <= n &&
           forall k : nat :: l <= k < i ==> V[k] < pivot &&
           forall k : nat :: i <= k < n ==> pivot <= V[k];
    m := i;
    assert i <= n;
    assert forall k : nat :: l <= k < i ==> V[k] < pivot;
    assert forall k : nat :: i <= k < n ==> pivot <= V[k];
}

method quicksort(i : nat, j : nat, V : array<int>)
    modifies V
    requires i <= j <= V.Length
    ensures forall k :: i <= k < j-1 ==> V[k] <= V[k+1]
    ensures forall k : nat :: (k < i || j <= k < V.Length) ==> old(V[k]) == V[k]
    decreases j - i
{
    if j - i >= 2 {
        var m := partition(i, j, V, V[i]);
        // If the pivot is in the array, then the middle index cannot
        // be out of bounds:
        assert i < m < j;
        quicksort(i, m, V);
        assert forall k :: i <= k < m-1 ==> V[k] <= V[k+1];
        quicksort(m, j, V);
        assert forall k :: i <= k < m-1 ==> V[k] <= V[k+1];
        assert V[m-1] <= V[m];
        assert forall k :: m <= k < j-1 ==> V[k] <= V[k+1];

        assert forall k :: i <= k < j-1 ==> V[k] <= V[k+1];
    } else {
        assert j - i < 2;
        assert j < i + 2;
        assert j <= i + 1;
        assert i <= j <= i + 1;
        assert j - i == 0 || j - i == 1;
        assert forall k :: i <= k < j-1 ==> V[k] <= V[k+1];
    }
}

method Main()
{
    var V := new int[5];
    V[0] := 5;
    V[1] := 4;
    V[2] := 3;
    V[3] := 2;
    V[4] := 1;
    var i := 0;
    while i < 5 {
        print V[i];
        print " ";
        i := i + 1;
    }
    print "\n";
    quicksort(0, V.Length, V);
    //print "m := ";
    //print m;
    //print "\n";
    i := 0;
    while i < 5 {
        print V[i];
        print " ";
        i := i + 1;
    }
    print "\n";
}

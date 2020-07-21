
predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
  requires 0 <= i <= j+1 <= a.Length
  reads a
{
  forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1)
  ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
{

  var i := 0;
  while i < a.Length
    decreases a.Length - i
    invariant 0 <= i <= a.Length
    invariant sorted_seg(a, 0, i-1)
    invariant multiset(a[ ..i]) == old(multiset(a[ ..i]))
    invariant a[i..] == old(a[i.. ])
  {
    var temp := a[i];
    var j := i;
    /*
    assert multiset(a[..i]) + multiset(a[i+1..i+1]) + multiset{temp}
      == multiset(a[..i]) + multiset{} + multiset{temp}
      == multiset(a[..i]) + multiset{temp}
      == old(multiset(a[..i]));
    */
    while j > 0 && temp < a[j - 1]
      decreases j
      modifies a
      invariant 0 <= j <= i < a.Length
      invariant sorted_seg(a, 0, j-1) && sorted_seg(a, j+1, i)
      invariant forall k, l :: 0 <= k <= j-1 && j+1 <= l <= i ==> a[k] <= a[l]
      invariant forall k :: j < k <= i ==> temp < a[k]
      //invariant j < i ==> a[j] == a[j+1]
      invariant a[i+1..] == old(a[i+1..])
      invariant j < i ==> multiset(a[..j]) + multiset(a[j+1..i+1]) + multiset{temp}
        == old(multiset(a[..i+1]))
      invariant j == i ==> multiset(a[..i+1]) == old(multiset(a[..i+1]))
      invariant j == i ==> temp == a[i]
    {
      if j < i {
        assert multiset(a[..j]) + multiset(a[j+1..i+1]) + multiset{temp}
          == old(multiset(a[..i+1]));
        assert multiset(a[..j-1]) + multiset{a[j-1]} + multiset(a[j+1..i+1]) + multiset{temp}
          == old(multiset(a[..i+1]));
        //assert multiset(a[..j-1]) + multiset(a[j..i+1]) + multiset{temp}
          //== old(multiset(a[..i+1]));
        /*
        assert multiset(a[..j]) + multiset(a[j+1..i+1]) + multiset{temp}
          == old(multiset(a[..i]));
        assert multiset(a[..j-1]) + multiset{a[j]}
            + multiset(a[j+1..i+1]) + multiset{temp}
          == old(multiset(a[..i]));
        assert multiset(a[..j-1]) + multiset(a[j..i+1]) + multiset{temp}
          == old(multiset(a[..i]));
          */
      } else {
        assert j == i;
        assert multiset(a[..i+1]) == old(multiset(a[..i+1]));
        assert multiset(a[..j+1]) == old(multiset(a[..i+1]));
        assert multiset(a[..j]) + multiset{a[j]} == multiset(a[..j+1]) == old(multiset(a[..i+1]));
        assert a[j] == a[i] == temp;
        assert multiset(a[..j]) + multiset{temp} == multiset(a[..j+1]) == old(multiset(a[..i+1]));
        assert multiset(a[..j-1]) + multiset{a[j-1]} + multiset{temp} == old(multiset(a[..i+1]));
      }
      a[j] := a[j - 1];
      if j < i {
        assert multiset(a[..j-1]) + (multiset{a[j]} + multiset(a[j+1..i+1])) + multiset{temp}
          == old(multiset(a[..i+1]));
        assert multiset(a[..j-1]) + multiset([a[j]] + a[j+1..i+1]) + multiset{temp}
          == old(multiset(a[..i+1]));
        assert [a[j]] + a[j+1..i+1] == a[j..i+1];
        assert multiset(a[..j-1]) + multiset(a[j..i+1]) + multiset{temp}
          == old(multiset(a[..i+1]));
      } else {
        assert j == i;
        //assert multiset(a[..j-1]) + multiset{a[j-1]} == multiset(a[..j]) == old(multiset(a[..i+1]));
        //assert multiset(a[..j-1]) + multiset(a[j..i+1]) == multiset(a[..j]) == old(multiset(a[..i+1]));
        //assert multiset(a[..j-1]) + multiset(a[j..i+1]) + multiset{temp} == old(multiset(a[..i+1]));
        assert multiset(a[..j-1]) + multiset{a[j]} + multiset{temp} == old(multiset(a[..i+1]));
      }
      j := j - 1;
      if j+1 < i {
        assert multiset(a[..j]) + multiset(a[j+1..i+1]) + multiset{temp}
          == old(multiset(a[..i+1]));
      } else {
        assert j+1 == i;
        assert multiset(a[..j]) + multiset(a[j+1..i+1]) + multiset{temp}
          == old(multiset(a[..i+1]));
      }
    }
    if j < i {
      assert multiset(a[..j]) + multiset(a[j+1..i+1]) + multiset{temp}
        == old(multiset(a[..i+1]));
    }
    a[j] := temp;
    if j < i {
      calc == {
        old(multiset(a[..i+1]));
        multiset(a[..j]) + multiset{a[j]} + multiset(a[j+1..i+1]);
        { assert [a[j]] + a[j+1..i+1] == a[j..i+1]; }
        multiset(a[..j]) + multiset(a[j..i+1]);
        { assert a[..j] + a[j..i+1] == a[..i+1]; }
        multiset(a[..i+1]);
      }
    } else {
      assert multiset(a[..i+1]) == old(multiset(a[..i+1]));
    }
    i := i + 1;
    assert multiset(a[..i]) == old(multiset(a[..i]));
  }
  assert multiset(a[ ..i]) == old(multiset(a[ ..i]));
  assert i == a.Length;
  assert multiset(a[ ..a.Length]) == old(multiset(a[ ..a.Length]));
  assert multiset(a[ ..a.Length]) == multiset(old(a[ ..a.Length]));
  assert a[..a.Length] == a[..];
  assert old(a[..a.Length]) == old(a[..]);
  assert multiset(a[..]) == old(multiset(a[..]));
}

include "../examples/reordenando-la-cola.dfy"
include "../src/linear/impl/LinkedStackImpl.dfy"
include "../src/linear/impl/SinglyLinkedQueueImpl.dfy"

method {:extern} Scan() returns (x: int)

method ScanArray(n: nat) returns (v: array<int>)
  ensures v.Length == n
  ensures fresh(v)
{
  v := new int[n];
  var i := 0;
  while i < n
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
    // assume n >= 0;
    if n == 0 {
      break;
    } else {
      var v := ScanArray(n);
      var neg := new LinkedStack();
      var pos := new SinglyLinkedQueue();
      // assert {v} !! {neg} + neg.Repr();
      // assert {v} !! {pos} + pos.Repr();
      // assert {pos} + pos.Repr() !! {neg} + neg.Repr();
      // assert neg.Valid();
      // assert neg.Empty();
      // assert pos.Valid();
      // assert pos.Empty();
      // assume forall i | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i+1]);
      reordenandoLaCola(neg, pos, v);
      var i := 0;
      while i < n
      {
        print v[i];
        if i != n-1 {
          print " ";
        }
        i := i + 1;
      }
      print "\n";
    }
  }
}

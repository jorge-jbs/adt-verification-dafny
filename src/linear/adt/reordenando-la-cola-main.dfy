include "../../../src/linear/adt/reordenando-la-cola.dfy"
include "../../../src/linear/adt/Stack.dfy"
include "../../../src/linear/adt/Queue1.dfy"

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

method Main()
  decreases *
{
  while true
    decreases *
  {
    var n := Scan();
    assume n >= 0;
    if n == 0 {
      break;
    } else {
      var v := ScanArray(n);
      var neg := new Stack1();
      var pos := new Queue1();
      assume {v} !! {neg} + neg.Repr();
      assert {v} !! {pos} + pos.Repr();
      assume {pos} + pos.Repr() !! {neg} + neg.Repr();
      assert neg.Valid();
      assert neg.Empty();
      assert pos.Valid();
      assert pos.Empty();
      assume forall i | 0 <= i < v.Length - 1 :: abs(v[i]) <= abs(v[i+1]);
      reordenandoLaCola(neg, pos, v);
    }
  }
}

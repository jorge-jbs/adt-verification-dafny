include "../src/linear/impl/LinkedStackImpl.dfy"
include "../examples/accidentes-aereos.dfy"

// method {:extern} Read() returns (x: int)
// method {:extern} ScanInt() returns (x: int)
// method {:extern} ScanString() returns (s: string)

method {:verify false} Main()
{
  var v := new nat[6];
  v[0] := 50;
  v[1] := 80;
  v[2] := 30;
  v[3] := 10;
  v[4] := 60;
  v[5] := 5;
  var st := new LinkedStack();
  var r := FindSummits(v, st);
  var i := 0;
  while i < r.Length
  {
    print r[i], " ";
    i := i + 1;
  }
}

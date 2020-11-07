include "../../../src/linear/adt/Stack.dfy"

method BalancedTest(s: string, st: Stack) returns (b: bool)
  modifies st.Repr()
  requires st.Valid()
  requires st.Model() == []
{
  // var st1 := new Stack1();
  // assert st1.Valid();
  // var st: Stack := st1;
  // assert st1.Valid();
  // assert st.Valid();
  var i := 0;
  // assert i !in st.Repr();
  while i < |s|
    modifies st.Repr()
    invariant fresh(st.Repr() - old(st.Repr()))
    invariant st.Valid()
  {
    /*
    ghost var orepr := st.Repr();
    st.Push(1);
    ghost var repr := st.Repr();
    assert repr > orepr;
    assert fresh(repr - orepr);
    */
    i := i + 1;
  }
}

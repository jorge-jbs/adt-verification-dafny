include "../../../src/linear/adt/Stack.dfy"

method BalancedTest(s: string) returns (b: bool)
{
  var st := new Stack<char>();
  var i := 0;
  while i < |s|
    modifies st, st.list
    invariant fresh(st)
    invariant fresh(st.list)
    // invariant fresh(st.list.head)
    invariant st.list.head == null
    invariant st.list.spine == []
    invariant forall x | x in st.list.spine :: fresh(x)
    invariant st.Valid()
  {
    assert fresh(st);
    assert fresh(st.list);
    assert st.list in {st.list};
    // st.Push('(');
    i := i + 1;
  }
}

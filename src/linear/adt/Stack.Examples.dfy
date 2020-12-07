include "../../../src/linear/adt/Stack.dfy"

function method OpeningBrace(c: char): (d: char)
  requires c == ')' || c == ']' || c == '}'
{
  if c == ')' then
    '('
  else if c == ']' then
    '['
  else
    '{'
}

method BalancedTest(s: string) returns (b: bool)
{
  var st := new Stack1();
  var i := 0;
  st.UselessLemma();
  while i < |s|
    modifies st.list
    // modifies st.Repr()
    invariant st.Valid()
  {
    assert fresh(st);
    if s[i] == '('  || s[i] == '[' || s[i] == '{' {
        st.Push(s[i] as int);
    } else if s[i] == ')' || s[i] == ']' || s[i] == '}' {
      if st.Empty() {
        return false;
      } else {
        var c := st.Pop();
        if c != OpeningBrace(s[i]) as int {
          return false;
        }
      }
    }
    i := i + 1;
  }
  return st.Empty();
}

method Main() {
  var b := BalancedTest("({}()");
  print(b);
}

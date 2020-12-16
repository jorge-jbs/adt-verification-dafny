include "../../../src/linear/adt/Stack.dfy"

// Works the same with `Stack` instead of `Stack1`.
method EvalPostfixAux(s: string, st: Stack1) returns (res: int)
  modifies st.Repr()
  requires st.Valid()
  requires forall c | c in s :: c in "0123456789+-*/"
{
  st.UselessLemma();
  if s == "" {
    if st.Empty() {
      return -1;
    }
    assert !st.Empty();
    res := st.Top();
  } else {
    var c := s[0];
    if c in "0123456789" {
      st.Push((c as int) - 48);
    } else {
      if st.Empty() {
        return -1;
      }
      var x := st.Pop();
      if st.Empty() {
        return -1;
      }
      var y := st.Pop();
      var n: int;
      if c == '+' {
        n := x + y;
      } else if c == '-' {
        n := x - y;
      } else if c == '*' {
        n := x * y;
      } else if c == '/' {
        if y == 0 {
          return -1;
        }
        assert y != 0;
        n := x / y;
      }
      st.Push(n);
    }
    res := EvalPostfixAux(s[1..], st);
  }
}

method EvalPostfix(s: string) returns (res: int)
  requires forall c | c in s :: c in "0123456789+-*/"
{
  var st := new Stack1();
  res := EvalPostfixAux(s, st);
}

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
  // var b := BalancedTest("({}()");
  // print(b);
  var n := EvalPostfix("12+3*");
  print(n);
}

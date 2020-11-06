include "../../../src/linear/implementation/SinglyLinkedListWithSpine.dfy"

// `Append` operation implemented externally.
method Append<A>(self: List<A>, other: List<A>)
  decreases self.Repr()
  modifies self
  requires self.Valid()
  requires other.Valid()
  // At first I didn't add the next precondition. In a language without
  // verification like C maybe I would have forgotten about it, but the function
  // doesn't work the way you expect it to if you don't keep this precondition
  // in mind. This could have resulted in segmentation faults or buggy code.
  // Another win for formal verification!
  requires self != other
  ensures self.Valid()
  ensures self.Model() == old(self.Model()) + other.Model()
{
  if self.head == null {
    self.Copy(other);
  } else {
    var x := self.Pop();
    Append(self, other);
    self.Push(x);
  }
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
  var st := new List<char>();
  var i := 0;
  while i < |s|
    modifies st
    invariant fresh(st)
    invariant st.Valid()
  {
    assert fresh(st);
    if s[i] == '('  || s[i] == '[' || s[i] == '{' {
      st.Push(s[i]);
    } else if s[i] == ')' || s[i] == ']' || s[i] == '}' {
      if st.head == null {
        return false;
      } else {
        var c := st.Pop();
        if c != OpeningBrace(s[i]) {
          return false;
        }
      }
    }
    i := i + 1;
  }
  return st.head == null;  // TODO: write `Empty` predicate
}

method Main() {
  var b := BalancedTest("({}())");
  print(b);
}

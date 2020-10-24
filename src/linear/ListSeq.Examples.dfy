include "../../src/linear/ListSeq.dfy"

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

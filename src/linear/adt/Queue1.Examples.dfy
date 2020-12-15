include "../../../src/linear/adt/Queue1.dfy"

method ItertatorExample() {
  var q: Queue1 := new Queue1();
  var it := new QueueIterator(q);
  while it.HasNext()
    invariant it.Valid()
    invariant it.parent == q
    decreases |q.Model()| - it.index
  {
    var x := it.Next();
    print(x);
  }
}

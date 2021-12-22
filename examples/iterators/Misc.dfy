include "../../src/linear/adt/List.dfy"
include "../../src/linear/impl/LinkedList.dfy"
include "../../src/linear/impl/VectorImpl.dfy"

method  IteratorExample1(l: List)
  modifies l,l.Repr()
  requires l.Valid()
  requires l.Model() != []
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)
{
  var it1 := l.Begin();
  var x := it1.Next();
}

method IteratorExample2(l: List)
  modifies l, l.Repr()
  requires l.Valid()
  requires l.Model() != []
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures l.Model() == old(l.Model())
  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)
{

  var it1 := l.Begin();
  var it2 := l.Begin();
}

method  IteratorExample3(l: LinkedList)
  modifies l, l.Repr()
  requires l.Valid()
  requires l.Model() != []
  requires forall x | x in l.Repr() :: allocated(x)
  ensures l.Valid()
  ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
  ensures fresh(l.Repr()-old(l.Repr()))
  ensures forall x | x in l.Repr() :: allocated(x)
{
  var it1 := l.Begin();
  var it2 := l.Begin();
  var x := it2.Next();
  var y := l.PopFront();
  assert x == y;
  //assert !it1.Valid();  // we cannot prove nor disprove this assertion
  assert it2.Valid();
}

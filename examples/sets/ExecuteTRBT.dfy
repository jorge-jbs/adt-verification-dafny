include "../../src/UnorderedMap/UnorderedMapSpec.dfy"
include "../../src/OrderedMap/OrderedMapSpec.dfy"
include "../../src/OrderedMap/OrderedMapImplTRBT.dfy"

module PruebaTRBT {
  import opened UnorderedMapSpec
  import opened OrderedMapSpec
  import opened OrderedMapImplTRBT

  method Populate(s: OrderedMap)
    modifies s, s.Repr()
    requires s.Valid()
    ensures s.Valid()

    ensures fresh(s.Repr()-old(s.Repr()))
  {
    s.Add(1, 0);
    s.Add(2, 1);
    s.Add(3, 9);
    s.Add(9, 2);
    s.Add(4, 3);
    s.Add(2, 5);
    s.Add(7, 3);
    s.Add(0, 2);
    s.Add(6, 2);
    s.Add(1, 7);
    s.Add(5, 2);
  }

  method Print(s: OrderedMap)
    modifies s, s.Repr()
    requires s.Valid()
    ensures s.Valid()

    ensures fresh(s.Repr()-old(s.Repr()))
  {
    var it := s.First();
    var hasPeek := it.HasPeek();
    while hasPeek
      decreases s.Model() - it.Traversed()
      invariant s.Valid()
      invariant it.Valid()
      invariant it.Parent() == s
      invariant hasPeek == it.HasPeek?()
      invariant fresh(s.Repr()-old(s.Repr()))
    {
      var p := it.Peek();
      print p.0;
      print " -> ";
      print p.1;
      print "\n";

      it.Next();
      hasPeek := it.HasPeek();
    }
  }

  method {:main} Main() {
    var s: OrderedMap := new OrderedMapImplTRBT();
    Populate(s);
    Print(s);
  }
}
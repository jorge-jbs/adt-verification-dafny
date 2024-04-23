include "../../src/UnorderedMap/UnorderedMapSpec.dfy"
include "../../src/UnorderedMap/UnorderedMapSpec.dfy"
include "../../src/TreeMap/TreeMapImpl.dfy"

module ExecuteTreeMap {
  import opened UnorderedMapSpec
  import opened TreeMapImpl

  method Populate(s: UnorderedMap)
    modifies s.Repr()
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

  opaque ghost function LoopBound(s: UnorderedMap, it: UnorderedMapIterator): nat
    reads s.Repr()
    requires Valid1It1(s, it)
  {
    reveal it.TraversedSpec();
    |s.Model()| - |it.Traversed()|
  }

  method Print(s: UnorderedMap)
    modifies s.Repr()
    requires s.Valid()
    ensures s.Valid()

    ensures fresh(s.Repr()-old(s.Repr()))
  {
    var it: UnorderedMapIterator := s.First();
    var hasPeek := it.HasPeek();
    while hasPeek
      decreases LoopBound(s, it)
      invariant s.Valid()
      invariant it.Valid()
      invariant it.Parent() == s
      invariant hasPeek == it.HasPeek?()
      invariant fresh(s.Repr()-old(s.Repr()))
    {
      label loopEntry:
      var p := it.Peek();
      print p.0;
      print " -> ";
      print p.1;
      print "\n";

      it.Next();
      hasPeek := it.HasPeek();

      assert LoopBound(s, it) < old@loopEntry(LoopBound(s, it)) by {
        reveal LoopBound();
        reveal it.PeekModel(), it.NextModel(), it.HasPeekModel();
      }
    }
  }

  method {:main} Main() {
    var s: UnorderedMap := new TreeMapImpl();
    Populate(s);
    Print(s);
  }
}
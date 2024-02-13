include "../../../src/Collections/KeyValue.dfy"
include "../../../src/UnorderedMap/UnorderedMapSpec.dfy"
include "../../../src/OrderedMap/OrderedMapSpec.dfy"
include "../../../src/TreeMap/TreeMapSpec.dfy"

module TreeMapImpl.EraseImpl {
  import opened KeyValue
  import opened UnorderedMapSpec
  import opened OrderedMapSpec
  import opened TreeMapSpec

  method Erase(self: TreeMap, mid: UnorderedMapIterator) returns (next: UnorderedMapIterator)
    modifies self, self.Repr()
    requires allocated(self.Repr())
    ensures fresh(self.Repr() - old(self.Repr()))
    ensures allocated(self.Repr())

    requires self.Valid()
    requires mid.Valid()
    requires mid.Parent() == self
    requires mid.HasPeek?()
    requires mid in self.Iterators()
    ensures self.Valid()
    ensures self.Model() == old(self.Model()) - {key(old(mid.Peek?()))}
    ensures |self.Model()| == |old(self.Model())| - 1

    ensures next is OrderedMapIterator
    ensures fresh(next)
    ensures next.Valid()
    ensures next.Parent() == self
    ensures next.Traversed() == old(mid.Traversed())
    ensures |next.Traversed()| == old(|mid.Traversed()|)

    ensures mid is OrderedMapIterator
    ensures (next as OrderedMapIterator).Index() == old((mid as OrderedMapIterator).Index())

    ensures self.Iterators() >= {next} + old(self.Iterators())
    ensures
      var k := old(mid.Peek?().0);
      forall it: OrderedMapIterator <- old(self.Iterators()) | 
          && old(it.Valid())
          && (old(it.HasPeek?()) ==> old(it.Peek?().0) != k)
        :: it.Valid()
        && it.Parent() == old(it.Parent())
        && (it.HasPeek?() <==> old(it.HasPeek?()))
        && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
        && (
          if (it.HasPeek?() ==> it.Peek?().0 < k) && old(it.Index()) != old(|self.Model()|) then
            it.Index() == old(it.Index())
          else
            it.Index() == old(it.Index()) - 1
        )
        && (
          if it.HasPeek?() && it.Peek?().0 < k then
            && it.Traversed() == old(it.Traversed())
            && |it.Traversed()| == |old(it.Traversed())|
          else
            && it.Traversed() == old(it.Traversed()) - {k}
            && |it.Traversed()| == |old(it.Traversed())| - 1
        )
  {
    next := self.Cast(mid).Copy();
    self.Cast(next).Next();
    var p := self.Cast(mid).Peek();
    self.Remove(p.0);
  }
}

include "../../src/UnorderedSet/UnorderedSetOpaqueSpec.dfy"

module UnordSetContained {
  import opened UnorderedSetSpec

  export provides UnorderedSetSpec, UnordSetContained

  // 41M RU (sin poscondición de iteradores)
  // 16M RU (con SameSpec no opaca)
  // 31M RU (con SameSpec opaca y reveal al final del bucle)
  // 9M RU (con ContainsModel opaca y reveal al final del bucle)
  // 30M RU (con ContainsModel y PeekModel opaca y reveal al final del bucle)
  // 20M RU (con *Model opaca y reveal al final del bucle)
  // 20M RU (con *Model opaca y `assert ... by { reveal ... }` al final del bucle)
  // 14M RU (con *Model opaca y dos `assert ... by { ... }` al final del bucle)
  // 51M RU (con *Model opaca y dos `assert ... by { ... }` al final del bucle, con AllIteratorsSame opaca)
  method UnordSetContained(s1: UnorderedSet, s2: UnorderedSet) returns (b: bool)
    modifies s1, s1.Repr(), s2, s2.Repr()
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())
    ensures fresh(s1.Repr()-old(s1.Repr()))
    ensures fresh(s2.Repr()-old(s2.Repr()))

    requires s1.Valid()
    requires s2.Valid()
    ensures s1.Valid()
    ensures s2.Valid()

    requires {s1} + s1.Repr() !! {s2} + s2.Repr()

    ensures s1.Model() == old(s1.Model())
    ensures s2.Model() == old(s2.Model())
    ensures b == (s1.Model() <= s2.Model())

    ensures s1.Iterators() >= old(s1.Iterators())
    ensures s2.Iterators() >= old(s2.Iterators())
  {
    var it1 := s1.First();

    b := true;
  label PreHasPeek:
    var it1HasPeek := it1.HasPeek();
    assert
      && it1.Parent().Model() == old@PreHasPeek(it1.Parent().Model())
      && |it1.Parent().Model()| == old@PreHasPeek(|it1.Parent().Model()|)
      && it1.Traversed() == old@PreHasPeek(it1.Traversed())
      && |it1.Traversed()| == old@PreHasPeek(|it1.Traversed()|)
    by {
      reveal it1.HasPeekModel();
    }

    while it1HasPeek && b
      decreases s1.Model() - it1.Traversed()
      invariant allocated(s1.Repr())
      invariant allocated(s2.Repr())
      invariant fresh(s1.Repr()-old(s1.Repr()))
      invariant fresh(s2.Repr()-old(s2.Repr()))

      invariant s1.Valid()
      invariant s2.Valid()
      invariant {s1} + s1.Repr() !! {s2} + s2.Repr()
      invariant s1.Model() == old(s1.Model())
      invariant s2.Model() == old(s2.Model())
      invariant it1.Valid()
      invariant it1 in s1.Iterators()
      invariant it1.Parent() == s1
      invariant it1.Traversed() <= s1.Model()
      invariant b == (it1.Traversed() <= s2.Model())
      invariant it1HasPeek == it1.HasPeek?()

      invariant s1.Iterators() >= old(s1.Iterators())
      invariant s2.Iterators() >= old(s2.Iterators())
    {
    label LoopBodyEntrance:
      var p := it1.Peek();
      //var it2: UnorderedSetIterator := s2.Find(p);
      //b := it2.HasPeek();
      b := s2.Contains(p);
      it1.Next();
      it1HasPeek := it1.HasPeek();
      assert
        && allocated(s1.Repr())
        && allocated(s2.Repr())
        && fresh(s1.Repr()-old(s1.Repr()))
        && fresh(s2.Repr()-old(s2.Repr()))
        && s1.Valid()
        && s2.Valid()
        && {s1} + s1.Repr() !! {s2} + s2.Repr()
        && it1.Valid()
        && it1 in s1.Iterators()
        && it1.Parent() == s1
        && it1HasPeek == it1.HasPeek?()
        && s1.Iterators() >= old(s1.Iterators())
        && s2.Iterators() >= old(s2.Iterators())
      by {
      }
      assert
        && s1.Model() == old(s1.Model())
        && s2.Model() == old(s2.Model())
        && it1.Traversed() <= s1.Model()
        && b == (it1.Traversed() <= s2.Model())
        && (s1.Model() - it1.Traversed()) < old@LoopBodyEntrance(s1.Model() - it1.Traversed())
      by {
      reveal it1.PeekModel();
      reveal s2.ContainsModel();
      reveal it1.NextModel();
      reveal it1.HasPeekModel();
      }
      /*
      assert
        && s1.Model() == old(s1.Model())
        && s2.Model() == old(s2.Model())
        && it1.Traversed() <= s1.Model()
        && b == (it1.Traversed() <= s2.Model())
      by {
        reveal s2.ContainsModel();
      }
      */
    }
  }
}
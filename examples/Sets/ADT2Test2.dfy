include "../../src/ADT.dfy"
include "../../src/Collections/KeyValue.dfy"
include "../../src/OrderedSet/OrderedSetSpec.dfy"
include "../../examples/Sets/ADT2.dfy"

module ADT2Test2 {
  import opened ADT
  import opened ADT2
  import opened OrderedSetSpec
  import opened KeyValue

  // 4.77M RU
  method Test1(t: ADT2<set<K>, set<K>>)
    modifies t.Repr()
    requires allocated(t.Repr())
    ensures fresh(t.Repr() - old(t.Repr()))

    requires t.Valid()
    requires t.a is OrderedSet
    requires t.b is OrderedSet
    ensures t.Valid()
  {
    var _ := (t.a as OrderedSet).Empty();
    t.ModifyA();
    var _ := (t.a as OrderedSet).Empty();
    t.ModifyA();
    var _ := (t.a as OrderedSet).Empty();
    t.ModifyA();
    var _ := (t.a as OrderedSet).Empty();
    t.ModifyA();
    var _ := (t.a as OrderedSet).Empty();
    t.ModifyA();
    var _ := (t.a as OrderedSet).Empty();
    t.ModifyA();
    var _ := (t.a as OrderedSet).Empty();
    t.ModifyA();
    var _ := (t.a as OrderedSet).Empty();
    t.ModifyA();
    var _ := (t.a as OrderedSet).Empty();
    t.ModifyA();
    var _ := (t.a as OrderedSet).Empty();
    t.ModifyA();
  }

  // 21.2M RU ==> 2.72M RU
  method Test1'(a: OrderedSet, b: OrderedSet)
    modifies a, a.Repr(), b, b.Repr()
    requires allocated(a.Repr())
    requires allocated(b.Repr())
    ensures fresh(a.Repr() - old(a.Repr()))
    ensures fresh(b.Repr() - old(b.Repr()))

    requires Valid2(a, b)
    ensures Valid2(a, b)
  {
    var _ := a.Empty();
    assert Valid2(a, b);
    var _ := a.Empty();
    assert Valid2(a, b);
    var _ := a.Empty();
    assert Valid2(a, b);
    var _ := a.Empty();
    assert Valid2(a, b);
    var _ := a.Empty();
    assert Valid2(a, b);
    var _ := a.Empty();
    assert Valid2(a, b);
    var _ := a.Empty();
    assert Valid2(a, b);
    var _ := a.Empty();
    assert Valid2(a, b);
    var _ := a.Empty();
    assert Valid2(a, b);
    var _ := a.Empty();
    assert Valid2(a, b);
  }

  // 24.5M RU
  method Test2(t: ADT2<set<K>, set<K>>)
    modifies t.Repr()
    requires allocated(t.Repr())
    ensures fresh(t.Repr() - old(t.Repr()))

    requires t.Valid()
    requires t.a is OrderedSet
    requires t.b is OrderedSet
    ensures t.Valid()
  {
    var _ := (t.a as OrderedSet).Empty();
    t.ModifyA();
  label L1:
    var _ := (t.b as OrderedSet).Empty();
    t.ModifyB@L1();
  label L2:
    var _ := (t.a as OrderedSet).Empty();
    t.ModifyA@L2();
  label L3:
    var _ := (t.b as OrderedSet).Empty();
    t.ModifyB@L3();
  label L4:
    var _ := (t.a as OrderedSet).Empty();
    t.ModifyA@L4();
  label L5:
    var _ := (t.b as OrderedSet).Empty();
    t.ModifyB@L5();
  }

  // 1.17M RU ==> 1.14M RU
  method Test2'(a: OrderedSet, b: OrderedSet)
    modifies a, a.Repr(), b, b.Repr()
    requires allocated(a.Repr())
    requires allocated(b.Repr())
    ensures fresh(a.Repr() - old(a.Repr()))
    ensures fresh(b.Repr() - old(b.Repr()))

    requires Valid2(a, b)
    ensures Valid2(a, b)
  {
    var _ := a.Empty();
    assert Valid2(a, b);
    var _ := b.Empty();
    assert Valid2(a, b);
    var _ := a.Empty();
    assert Valid2(a, b);
    var _ := b.Empty();
    assert Valid2(a, b);
    var _ := a.Empty();
    assert Valid2(a, b);
    var _ := b.Empty();
    assert Valid2(a, b);
  }

  // 2.71M RU
  method Test3'(a: OrderedSet, itA: OrderedSetIterator, b: OrderedSet, itB: OrderedSetIterator)
    modifies a, a.Repr(), b, b.Repr()
    requires allocated(a.Repr())
    requires allocated(b.Repr())
    ensures fresh(a.Repr() - old(a.Repr()))
    ensures fresh(b.Repr() - old(b.Repr()))

    requires Valid2It11(a, itA, b, itB)
    ensures Valid2It11(a, itA, b, itB)
  {
    var _ := a.Empty();
    assert Valid2It11(a, itA, b, itB);
    var _ := b.Empty();
    assert Valid2It11(a, itA, b, itB);
    var _ := a.Empty();
    assert Valid2It11(a, itA, b, itB);
    var _ := b.Empty();
    assert Valid2It11(a, itA, b, itB);
    var _ := a.Empty();
    assert Valid2It11(a, itA, b, itB);
    var _ := b.Empty();
    assert Valid2It11(a, itA, b, itB);
  }

  // 1.82M RU
  method Test4'(a: OrderedSet, itA: OrderedSetIterator, b: OrderedSet, itB: OrderedSetIterator)
    modifies a, a.Repr(), b, b.Repr()
    requires allocated(a.Repr())
    requires allocated(b.Repr())
    ensures fresh(a.Repr() - old(a.Repr()))
    ensures fresh(b.Repr() - old(b.Repr()))

    requires Valid2It11(a, itA, b, itB)
    requires itA.HasPeek?()
    ensures Valid2It11(a, itA, b, itB)
  {
    itA.Next();
    var _ := itA.HasPeek();
    var _ := itB.HasPeek();
  }

  // 1.72M RU
  method Test5'(a: OrderedSet, itA: OrderedSetIterator, b: OrderedSet, itB: OrderedSetIterator)
    modifies a, a.Repr(), b, b.Repr()
    requires allocated(a.Repr())
    requires allocated(b.Repr())
    ensures fresh(a.Repr() - old(a.Repr()))
    ensures fresh(b.Repr() - old(b.Repr()))

    requires Valid2It11(a, itA, b, itB)
    requires itB.HasPeek?()
    ensures Valid2It11(a, itA, b, itB)
  {
    itB.Next();
    var _ := itB.HasPeek();
    var _ := itA.HasPeek();
  }

  // 5.99M RU
  method Test6'(a: OrderedSet, itA: OrderedSetIterator, b: OrderedSet, itB: OrderedSetIterator)
    modifies a, a.Repr(), b, b.Repr()
    requires allocated(a.Repr())
    requires allocated(b.Repr())
    ensures fresh(a.Repr() - old(a.Repr()))
    ensures fresh(b.Repr() - old(b.Repr()))

    requires Valid2It11(a, itA, b, itB)
    requires itA.HasPeek?()
    requires itB.HasPeek?()
    ensures Valid2It11(a, itA, b, itB)
  {
    itA.Next();
    var _ := itA.HasPeek();
    itB.Next();
    var _ := itB.HasPeek();
  }

  // 1 -  717K RU
  // 2 - 2.93M RU
  // 3 - 9.40M RU (~25.4s)
  method Test7'(a: OrderedSet, itA: OrderedSetIterator, b: OrderedSet, itB: OrderedSetIterator)
    modifies a, a.Repr(), b, b.Repr()
    requires allocated(a.Repr())
    requires allocated(b.Repr())
    ensures fresh(a.Repr() - old(a.Repr()))
    ensures fresh(b.Repr() - old(b.Repr()))

    requires Valid2It11(a, itA, b, itB)
    ensures Valid2It11(a, itA, b, itB)
  {
    var b := itA.HasPeek();
    if b {
      itA.Next();
      var b := itB.HasPeek();
      if b {
        itB.Next();
        var b := itA.HasPeek();
        if b {
          itA.Next();
          /*
          var b := itB.HasPeek();
          if b {
            itB.Next();
          }
          */
        }
      }
    }
  }

  // 1  -  623K RU
  // 2  - 2.33M RU
  // 3  - 13.4M RU  (~21s)
  // 3½ - 16.6M RU
  // 4  - 27.7M RU
  method {:only} Test8'(a: OrderedSet, itA: OrderedSetIterator, b: OrderedSet, itB: OrderedSetIterator)
    modifies a, a.Repr(), b, b.Repr()
    requires allocated(a.Repr())
    requires allocated(b.Repr())
    ensures fresh(a.Repr() - old(a.Repr()))
    ensures fresh(b.Repr() - old(b.Repr()))

    requires Valid2It11(a, itA, b, itB)
    ensures Valid2It11(a, itA, b, itB)
  {
    var hp := itA.HasPeek();
    assert Valid2It11(a, itA, b, itB);
    if hp {
      itA.Next();
      assert Valid2It11(a, itA, b, itB);
      var hp := itB.HasPeek();
      assert Valid2It11(a, itA, b, itB);
      if hp {
        itB.Next();
        assert Valid2It11(a, itA, b, itB);
        var hp := itA.HasPeek();
        assert Valid2It11(a, itA, b, itB);
        if hp {
          itA.Next();
          assert Valid2It11(a, itA, b, itB);
          var hp := itB.HasPeek();
          assert Valid2It11(a, itA, b, itB);
          if hp {
            itB.Next();
            assert Valid2It11(a, itA, b, itB);
      /*
            var hp := itA.HasPeek();
            assert Valid2It11(a, itA, b, itB);
            if hp {
              itA.Next();
              assert Valid2It11(a, itA, b, itB);
              var hp := itB.HasPeek();
              assert Valid2It11(a, itA, b, itB);
              if hp {
                itB.Next();
                assert Valid2It11(a, itA, b, itB);
              }
            }
      */
          }
        }
      }
    }
  }

  // 518K RU
  method {:only} Test11'(a: OrderedSet, itA: OrderedSetIterator, itB: OrderedSetIterator)
    modifies a, a.Repr()
    requires allocated(a.Repr())
    ensures fresh(a.Repr() - old(a.Repr()))

    requires ValidIt2(a, itA, itB)
    requires itA.HasPeek?()
    requires itB.HasPeek?()
    requires itA.Peek?() != itB.Peek?()
    ensures a.Valid()
    ensures ValidIt(a, itB)
  {
    var _ := a.Erase(itA);
    itB.Next();
  }
}
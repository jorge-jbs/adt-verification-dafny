include "../../src/ADT.dfy"
include "../../src/Collections/KeyValue.dfy"
include "../../src/OrderedSet/OrderedSetSpec2.dfy"
include "../../examples/Sets/ADT2.dfy"

module ADT2Test {
  import opened ADT
  import opened ADT2
  import opened OrderedSetSpec2
  import opened KeyValue

  // 4.85M RU
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

  // 8.31M RU ==> 2.26M RU
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

  // 6.67M RU
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

  // 1.01M RU ==> 876K RU
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
    //assert Valid2(a, b);
    var _ := b.Empty();
    //assert Valid2(a, b);
    var _ := a.Empty();
    //assert Valid2(a, b);
    var _ := b.Empty();
    //assert Valid2(a, b);
    var _ := a.Empty();
    //assert Valid2(a, b);
    var _ := b.Empty();
    //assert Valid2(a, b);
  }
  
  // 1.91M RU
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
    a.SameIterator(itA);
    assert Valid2It11(a, itA, b, itB);
  label L1:
    var _ := b.Empty();
    b.SameIterator@L1(itB);
    assert Valid2It11(a, itA, b, itB);
  label L2:
    var _ := a.Empty();
    a.SameIterator@L2(itA);
    assert Valid2It11(a, itA, b, itB);
  label L3:
    var _ := b.Empty();
    b.SameIterator@L3(itB);
    assert Valid2It11(a, itA, b, itB);
  label L4:
    var _ := a.Empty();
    a.SameIterator@L4(itA);
    assert Valid2It11(a, itA, b, itB);
  label L5:
    var _ := b.Empty();
    b.SameIterator@L5(itB);
    assert Valid2It11(a, itA, b, itB);
  }

  // 653K RU
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

  // 635K RU
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

  // 1.01M RU
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

  // 1 -  423K RU
  // 2 - 1.02M RU
  // 3 - 3.11M RU
  // 4 - 8.22M RU  (~12.8s)
  method Test7'(a: OrderedSet, itA: OrderedSetIterator, b: OrderedSet, itB: OrderedSetIterator)
    modifies a, a.Repr(), b, b.Repr()
    requires allocated(a.Repr())
    requires allocated(b.Repr())
    ensures fresh(a.Repr() - old(a.Repr()))
    ensures fresh(b.Repr() - old(b.Repr()))

    requires Valid2It11(a, itA, b, itB)
    ensures Valid2It11(a, itA, b, itB)
  {
    var hp := itA.HasPeek();
    if hp {
      itA.Next();
      var hp := itB.HasPeek();
      if hp {
        itB.Next();
        var hp := itA.HasPeek();
        if hp {
          itA.Next();
          var hp := itB.HasPeek();
          if hp {
            itB.Next();
          }
        }
      }
    }
  }

  // 1  -  399K RU
  // 2  -  751K RU
  // 3  - 1.85M RU
  // 4  - 2.96M RU
  // 5  - 3.05M RU
  // 6  - 6.27M RU
  // 7  - 8.68M RU
  // 8  - 11.6M RU
  // 9  - 17.7M RU
  // 10 - 20.5M RU
  // 11 - 24.5M RU
  // 12 - 31.9M RU
  method Test8'(a: OrderedSet, itA: OrderedSetIterator, b: OrderedSet, itB: OrderedSetIterator)
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
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  // 3.06M RU
  method Test9'(a: OrderedSet, itA: OrderedSetIterator, b: OrderedSet, itB: OrderedSetIterator)
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
      var hp := itB.HasPeek();
      assert Valid2It11(a, itA, b, itB);
      itA.Next();
      assert Valid2It11(a, itA, b, itB);
      if hp {
        var hp := itA.HasPeek();
        assert Valid2It11(a, itA, b, itB);
        itB.Next();
        assert Valid2It11(a, itA, b, itB);
        if hp {
          var hp := itB.HasPeek();
          assert Valid2It11(a, itA, b, itB);
          itA.Next();
          assert Valid2It11(a, itA, b, itB);
          if hp {
            itB.Next();
            assert Valid2It11(a, itA, b, itB);
          }
        }
      }
    }
  }

  method Test10'(a: OrderedSet, itA: OrderedSetIterator, b: OrderedSet, itB: OrderedSetIterator)
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
    assert Valid2It11(a, itA, b, itB);
  label L1:
    var _ := a.Empty();
    a.SameIterator@L1(itA);
    assert Valid2It11(a, itA, b, itB);
    var _ := itA.HasPeek();
    assert Valid2It11(a, itA, b, itB);
    itB.Next();
    assert Valid2It11(a, itA, b, itB);
  label L2:
    var _ := a.Empty();
    a.SameIterator@L2(itA);
    assert Valid2It11(a, itA, b, itB);
    var _ := itB.HasPeek();
    assert Valid2It11(a, itA, b, itB);
  }

  // 327K RU
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
    a.EraseIteratorHP(itA, itB);
    itB.Next();
  }
}
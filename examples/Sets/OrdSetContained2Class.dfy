include "../../src/ADT.dfy"
include "../../src/OrderedSet/OrderedSetSpec2.dfy"
include "../../src/Collections/Int.dfy"

module OrdSetContained {
  import opened OrderedSetSpec2
  import opened ADT
  import opened Int

  //xport provides ADT, OrderedSetSpec2, OrdSetContained

  class OrdSetContainedLoop extends ADT<()> {
    const s1: OrderedSet
    const s2: OrderedSet
    const it1: OrderedSetIterator
    const it2: OrderedSetIterator
    var it1HasPeek: bool
    var it2HasPeek: bool

    ghost function ReprFamily(n: nat): set<object>
      decreases n
      //ensures forall i, j | 0 <= i < j <= n :: ReprFamily(i) <= ReprFamily(j)
      ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
      reads this, if n == 0 then {} else ReprFamily(n-1)
    {
    if n == 0 then
      {s1, s2}
    else if n <= s1.ReprDepth + 1 && n <= s2.ReprDepth + 1 then
      {s1, s2} + s1.ReprFamily(n-1) + s2.ReprFamily(n-1)
    else if n > s1.ReprDepth + 1 && n <= s2.ReprDepth + 1 then
      {s1, s2} + s1.Repr() + s2.ReprFamily(n-1)
    else if n <= s1.ReprDepth + 1 && n > s2.ReprDepth + 1 then
      {s1, s2} + s1.ReprFamily(n-1) + s2.Repr()
    else
      {s1, s2} + s1.Repr() + s2.Repr()
    }

    ghost predicate Valid()
      reads this, Repr()
    {
      && ReprDepth == Max(s1.ReprDepth, s2.ReprDepth) + 1
      && assert ReprFamily(0) <= ReprFamily(ReprDepth); true
      //&& {s1} + s1.Repr() !! {s2} + s2.Repr()
      && Valid2(s1, s2)
      && this !in {s1} + s1.Repr()
      && this !in {s2} + s2.Repr()
      //&& s1.Valid()
      //&& s2.Valid()
    }

    ghost function Model(): ()
      reads this, Repr()
      requires Valid()
    {
      ()
    }

    constructor(s1: OrderedSet, s2: OrderedSet)
      modifies s1, s1.Repr(), s2, s2.Repr()
      requires allocated(s1.Repr())
      requires allocated(s2.Repr())
      ensures allocated(s1.Repr())
      ensures allocated(s2.Repr())
      requires Valid2(s1, s2)
      ensures MaintainsValid2(s1, s2)
      //ensures Valid()
      //ensures fresh(Repr())
      //ensures allocated(Repr())
    {
      //assert {s1} + s1.Repr() !! {s2} + s2.Repr();
      var it1' := s1.First();
      MaintainsValid2Helper(s1, s2);
      it1 := it1';
    label L1:
      var it2' := s2.First();
      MaintainsValid2Helper@L1(s2, s1);
      it2 := it2';
      assert MaintainsValid2(s1, s2);
      this.s1 := s1;
      this.s2 := s2;
      ReprDepth := Max(s1.ReprDepth, s2.ReprDepth) + 1;
      assert MaintainsValid2(s1, s2);
      new;
    label L2:
      assert Valid2It11(s1, it1, s2, it2);
      assert it1 in s1.Iterators();
      assert allocated(s1.Repr());
      assert allocated(s2.Repr());
      it1HasPeek := it1.HasPeek();
      MaintainsValid2It11Helper@L2(s1, it1, s2, it2);
      assert old@L2(it1 in s1.Iterators());
      assert MaintainsValid2It11@L2(s1, it1, s2, it2);
      assert MaintainsValid2(s1, s2);
      assume false;
      it2HasPeek := it2.HasPeek();
      //assert Repr() == {s1, s2} + s1.Repr() + s2.Repr();
    }
  }
}
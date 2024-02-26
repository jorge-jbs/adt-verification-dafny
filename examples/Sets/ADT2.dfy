include "../../src/ADT.dfy"
include "../../src/Collections/Int.dfy"

module ADT2 {
  import opened ADT
  import opened Int

  //xport provides ADT, OrderedSetSpec2, OrdSetContained

  class ADT2<A, B> extends ADT<(A, B)> {
    const a: ADT<A>
    const b: ADT<B>

    ghost function ReprFamily(n: nat): set<object>
      decreases n
      //ensures forall i, j | 0 <= i < j <= n :: ReprFamily(i) <= ReprFamily(j)
      ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
      reads this, if n == 0 then {} else ReprFamily(n-1)
      /*
      ensures n >= a.ReprDepth + 1 && n >= b.ReprDepth + 1 ==>
        && ReprFamily(n) == {a, b} + a.Repr() + b.Repr()
        && a.Repr() <= ReprFamily(n)
        && b.Repr() <= ReprFamily(n)
        */
    {
      if n == 0 then
        {a, b}
      else if n <= a.ReprDepth + 1 && n <= b.ReprDepth + 1 then
        {a, b} + a.ReprFamily(n-1) + b.ReprFamily(n-1)
      else if n > a.ReprDepth + 1 && n <= b.ReprDepth + 1 then
        {a, b} + a.Repr() + b.ReprFamily(n-1)
      else if n <= a.ReprDepth + 1 && n > b.ReprDepth + 1 then
        {a, b} + a.ReprFamily(n-1) + b.Repr()
      else
        {a, b} + a.Repr() + b.Repr()
    }

    ghost predicate Valid()
      reads this, Repr()
    {
      && ReprDepth == Max(a.ReprDepth, b.ReprDepth) + 1
      && assert ReprFamily(0) <= ReprFamily(ReprDepth);
      //&& {a} + a.Repr() !! {b} + b.Repr()
      && Valid2(a, b)
      && this !in {a} + a.Repr()
      && this !in {b} + b.Repr()
      //&& a.Valid()
      //&& b.Valid()
    }

    ghost function Model(): (A, B)
      reads this, Repr()
      requires Valid()
    {
      (a.Model(), b.Model())
    }

    constructor(a: ADT<A>, b: ADT<B>)
      modifies a, a.Repr(), b, b.Repr()
      requires allocated(a.Repr())
      requires allocated(b.Repr())
      ensures allocated(a.Repr())
      ensures allocated(b.Repr())
      requires Valid2(a, b)
      ensures MaintainsValid2(a, b)
      ensures Valid()
      //ensures fresh(Repr())
      //ensures allocated(Repr())
    {
      this.a := a;
      this.b := b;
      ReprDepth := Max(a.ReprDepth, b.ReprDepth) + 1;
    }

    twostate lemma ModifyA()
      requires old(allocated(Repr()))

      requires old(Valid())
      requires a.Valid()
      requires fresh(a.Repr() - old(a.Repr()))
      requires b.Repr() == old(b.Repr())
      requires unchanged({b} + b.Repr())
      ensures Valid()
    {}

    twostate lemma ModifyB()
      requires old(allocated(Repr()))

      requires old(Valid())
      requires b.Valid()
      requires fresh(b.Repr() - old(b.Repr()))
      requires a.Repr() == old(a.Repr())
      requires unchanged({a} + a.Repr())
      ensures Valid()
    {}
  }
}
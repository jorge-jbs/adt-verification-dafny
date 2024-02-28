include "../../src/Collections/KeyValue.dfy"
include "../../src/Collections/SetObject.dfy"

module OrdSetIntersection2 {
  import opened KeyValue
  import opened SetObject

  type pos = n: int | n > 0 witness 1

  trait {:termination false} ADT<M> {
    ghost const ReprDepth: pos

    ghost function ReprFamily(n: nat): set<object>
      decreases n
      //ensures forall i, j | 0 <= i < j <= n :: ReprFamily(i) <= ReprFamily(j)
      ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
      reads if n == 0 then {} else ReprFamily(n-1)

    ghost function Repr(): set<object>
      reads ReprFamily(ReprDepth-1)
    {
      ReprFamily(ReprDepth)
    }

    lemma ReprLemma()
      ensures Repr() == ReprFamily(ReprDepth)
    {}

    ghost predicate Valid()
      reads Repr()

    ghost function Model(): M
      reads Repr()
      requires Valid()
  }

  datatype ADT2<A, B> = ADT2(a: ADT<A>, b: ADT<B>)
  {
    ghost function Repr(): set<object>
      reads a, a.ReprFamily(a.ReprDepth-1)
      reads b, b.ReprFamily(b.ReprDepth-1)
    {
      {a} + a.Repr() + {b} + b.Repr()
    }

    ghost predicate Valid()
      reads Repr()
      //reads a, a.Repr(), b, b.Repr()
      ensures Valid() ==> a.Valid()
      ensures Valid() ==> b.Valid()
    {
      && a.Valid()
      && b.Valid()
      //&& {a} + a.Repr() !! {b} + b.Repr()
      && a.Repr() !! b.Repr()
      && a !in b.Repr()
      && b !in a.Repr()
      && a != b
    }
  }

  ghost predicate Valid2<A, B>(a: ADT<A>, b: ADT<B>)
    reads a, a.Repr(), b, b.Repr()
    ensures Valid2(a, b) ==> a.Valid()
    ensures Valid2(a, b) ==> b.Valid()
  {
    && a.Valid()
    && b.Valid()
    //&& {a} + a.Repr() !! {b} + b.Repr()
    && a.Repr() !! b.Repr()
    && a !in b.Repr()
    && b !in a.Repr()
    && a != b
  }

  twostate predicate MaintainsValid2<A, B>(a: ADT<A>, b: ADT<B>)
    reads a, a.Repr(), b, b.Repr()
    requires old(Valid2(a, b))
  {
    && Valid2(a, b)
    && fresh(a.Repr() - old(a.Repr()))
    && fresh(b.Repr() - old(b.Repr()))
  }

  datatype ADT3<A, B, C> = ADT3(a: ADT<A>, b: ADT<B>, c: ADT<C>)
  {
    ghost function Repr(): set<object>
      reads a, a.ReprFamily(a.ReprDepth-1)
      reads b, b.ReprFamily(b.ReprDepth-1)
      reads c, c.ReprFamily(c.ReprDepth-1)
    {
      {a} + a.Repr() + {b} + b.Repr() + {c} + c.Repr()
    }

    twostate predicate Fresh()
      reads Repr()
    {
      && fresh(a.Repr() - old(a.Repr()))
      && fresh(b.Repr() - old(b.Repr()))
      && fresh(c.Repr() - old(c.Repr()))
    }

    ghost predicate {:inline} Valid()
      //reads a, a.Repr(), b, b.Repr(), c, c.Repr()
      reads Repr()
      ensures Valid() ==> a.Valid()
      ensures Valid() ==> b.Valid()
      ensures Valid() ==> c.Valid()
    {
      && a.Valid()
      && b.Valid()
      && c.Valid()

      //&& {a} + a.Repr() !! {b} + b.Repr()
      && a.Repr() !! b.Repr()
      && a !in b.Repr()
      && b !in a.Repr()
      && a != b

      //&& {a} + a.Repr() !! {c} + c.Repr()
      && a.Repr() !! c.Repr()
      && a !in c.Repr()
      && c !in a.Repr()
      && a != c

      //&& {b} + b.Repr() !! {c} + c.Repr()
      && b.Repr() !! c.Repr()
      && b !in c.Repr()
      && c !in b.Repr()
      && b != c
    }
  }

  twostate lemma MaintainsValid2Helper<A, B>(a: ADT<A>, b: ADT<B>)
    requires a.Valid()
    requires fresh(a.Repr() - old(a.Repr()))

    requires old(allocated(a.Repr()))
    requires old(allocated(b.Repr()))
    requires allocated(b.Repr())
    requires b.Repr() == old(b.Repr())
    requires unchanged({b} + b.Repr())

    //requires old(a.Repr()) !! b.Repr()
    requires old(Valid2(a, b))

    ensures MaintainsValid2(a, b)
    ensures allocated(a.Repr())
    ensures allocated(b.Repr())
  {
    //reveal Valid2();
  }

  ghost predicate Valid3<A, B, C>(a: ADT<A>, b: ADT<B>, c: ADT<C>)
    reads a, a.Repr(), b, b.Repr(), c, c.Repr()
    ensures Valid3(a, b, c) ==> a.Valid()
    ensures Valid3(a, b, c) ==> b.Valid()
    ensures Valid3(a, b, c) ==> c.Valid()
  {
    && a.Valid()
    && b.Valid()
    && c.Valid()

    //&& {a} + a.Repr() !! {b} + b.Repr()
    && a.Repr() !! b.Repr()
    && a != b

    //&& {a} + a.Repr() !! {c} + c.Repr()
    && a.Repr() !! c.Repr()
    && a != c

    //&& {b} + b.Repr() !! {c} + c.Repr()
    && b.Repr() !! c.Repr()
    && b != c
  }

  twostate lemma MaintainsValid3Helper<A, B, C>(a: ADT<A>, b: ADT<B>, c: ADT<C>)
    requires a.Valid()
    requires fresh(a.Repr() - old(a.Repr()))

    requires old(allocated(a.Repr()))
    requires old(allocated(b.Repr()))
    requires old(allocated(c.Repr()))
    requires allocated(b.Repr())
    requires allocated(c.Repr())
    requires b.Repr() == old(b.Repr())
    requires c.Repr() == old(c.Repr())
    requires unchanged(b.Repr())
    requires unchanged(c.Repr())

    requires old(Valid3(a, b, c))

    ensures Valid3(a, b, c)
    ensures fresh(a.Repr() - old(a.Repr()))
    ensures fresh(b.Repr() - old(b.Repr()))
    ensures fresh(c.Repr() - old(c.Repr()))
    ensures allocated(a.Repr())
    ensures allocated(b.Repr())
    ensures allocated(c.Repr())
  {}

  trait OrderedSetIterator {
    ghost function Parent(): OrderedSet

    ghost predicate Valid()
      reads Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()

    ghost predicate HasPeek?()
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()

    ghost predicate PastTheEnd?()
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures PastTheEnd?() ==> !HasPeek?()

    ghost predicate PastTheBeginning?()
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures PastTheBeginning?() ==> !HasPeek?()
    {
      !HasPeek?() && !PastTheEnd?()
    }

    opaque ghost predicate BeforeSpec(before: set<K>)
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
    {
      && before < Parent().Model()
      && |before| < |Parent().Model()|
    }

    ghost function Before(): set<K>
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures BeforeSpec(Before())

    opaque ghost predicate Before'Spec(before': set<K>)
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
    {
      && before' <= Parent().Model()
      && 0 <= |before'| <= |Parent().Model()|
    }

    ghost function Before'(): set<K>
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures Before'Spec(Before'())
    {
      if HasPeek?() then
        assert Before'Spec(Before()) by { reveal BeforeSpec(), Before'Spec(); }
        Before()
      else if PastTheEnd?() then
        assert Before'Spec(Parent().Model()) by { reveal BeforeSpec(), Before'Spec(); }
        Parent().Model()
      else
        assert Before'Spec({}) by { reveal BeforeSpec(), Before'Spec(); }
        {}
    }

    opaque ghost function After(): set<K>
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
    {
      (Parent().Model() - Before'()) - {Peek?()}
    }

    ghost function After'(): set<K>
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
    {
      if HasPeek?() then
        After()
      else if PastTheBeginning?() then
        {}
      else
        Parent().Model()
    }

    opaque ghost predicate PeekSpec(p: K)
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
    {
      && p in Parent().Model()
      && p !in Before()
      && (forall x <- Before() :: x < p)
      && (forall x <- Parent().Model() | x !in Before() :: p <= x)
    }

    ghost function Peek?(): K
      reads Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures PeekSpec(Peek?())

    opaque twostate predicate HasPeekModel()
      reads Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
      requires old(HasPeek?()) ==> HasPeek?()
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && Before'() == old(Before'())
      && |Before'()| == old(|Before'()|)
      && (old(HasPeek?()) ==> Peek?() == old(Peek?()))
      && PastTheEnd?() == old(PastTheEnd?())
    }

    method HasPeek() returns (b: bool)
      modifies Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      ensures Valid()
      ensures Parent().Valid()
      //ensures Parent() == old(Parent())
      ensures b <==> HasPeek?() //== old(HasPeek?())
      ensures Parent().Iterators() >= old(Parent().Iterators())
      //ensures PastTheEnd?() == old(PastTheEnd?())
      ensures HasPeekModel()
      /*
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))
      */

    opaque twostate predicate PeekModel(p: K)
      reads Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
      requires old(HasPeek?())
      requires HasPeek?()
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && Before'() == old(Before'())
      && |Before'()| == old(|Before'()|)
      && p == Peek?() == old(Peek?())
    }

    method Peek() returns (p: K)
      modifies Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      //ensures Parent() == old(Parent())
      ensures HasPeek?()
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures PeekModel(p)
      /*
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))
                */

    opaque twostate predicate NextModel()
      reads Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
      requires old(HasPeek?())
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && Before'() == {old(Peek?())} + old(Before())
      && |Before'()| == 1 + old(|Before()|)
    }

    method Next()
      modifies Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      //ensures Parent() == old(Parent())
      ensures Parent().Iterators() >= old(Parent().Iterators())
      //ensures !PastTheBeginning?()
      ensures NextModel()
      /*
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && (it != this ==> it.Traversed() == old(it.Traversed())
                                   && |it.Traversed()| == old(|it.Traversed()|)
                                   && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?())))
      */

    opaque twostate predicate PrevModel()
      reads Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
      requires old(HasPeek?())
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && After'() == {old(Peek?())} + old(After())
      && |After'()| == 1 + old(|After()|)
    }

    method Prev()
      modifies Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      //ensures Parent() == old(Parent())
      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures PrevModel()

    opaque twostate predicate CopyModel()
      reads Parent().Repr()
      requires old(Valid())
      requires old(Parent().Valid())
      requires Valid()
      requires Parent().Valid()
    {
      && Parent().Model() == old(Parent().Model())
      && |Parent().Model()| == old(|Parent().Model()|)
      && Before'() == old(Before'())
      && |Before'()| == old(|Before'()|)
    }
  }

  trait OrderedSet extends ADT<set<K>> {
    ghost function Iterators(): set<OrderedSetIterator>
      reads Repr()
      requires Valid()
      ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this

    opaque twostate predicate EmptyModel(b: bool)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && b == (Model() == {})
    }

    opaque twostate predicate SameIteratorModel(it: OrderedSetIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires it.Valid()
      requires it.HasPeek?() == old(it.HasPeek?())
    {
      && it.Before'() == old(it.Before'())
      && |it.Before'()| == old(|it.Before'()|)
      && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
    }

    opaque twostate predicate SameIterators()
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
    {
      assert old(Allocated(Repr()); true);  // am I breaking something?
      forall it <- old(Iterators()) | old(it.Valid()) ::
        && it.Valid()
        && it.HasPeek?() == old(it.HasPeek?())
        && SameIteratorModel(it)
        //&& it.Parent() == old(it.Parent())
    }

    twostate lemma SameIterator(it: OrderedSetIterator)
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires SameIterators()
      ensures it.Valid()
      ensures it.HasPeek?() == old(it.HasPeek?())
      ensures SameIteratorModel(it)
    {
      reveal SameIterators();
    }

    method Empty() returns (b: bool)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures EmptyModel(b)
      ensures SameIterators()

    opaque twostate predicate SizeModel(s: nat)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && s == |Model()|
    }

    method Size() returns (s: nat)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures SizeModel(s)
      ensures SameIterators()

    opaque twostate predicate FirstModel(new it: OrderedSetIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires it.Valid()
      requires it.Parent() == this
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && it.Before'() == {}
    }

    method First() returns (it: OrderedSetIterator)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()

      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures !it.PastTheBeginning?()
      ensures Iterators() >= {it} + old(Iterators())

      ensures FirstModel(it)
      ensures SameIterators()

    opaque twostate predicate LastModel(new it: OrderedSetIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires it.Valid()
      requires it.Parent() == this
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && it.After'() == {}
    }

    method Last() returns (it: OrderedSetIterator)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()

      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures Iterators() >= {it} + old(Iterators())

      ensures LastModel(it)

    opaque twostate predicate ContainsModel(k: K, b: bool)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && b == (k in Model())
    }

    method Contains(k: K) returns (b: bool)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures ContainsModel(k, b)

    opaque twostate predicate AddModel(k: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model()) + {k}
      && if k in old(Model()) then
        |Model()| == old(|Model()|)
      else
        |Model()| == old(|Model()|) + 1
    }

    method Add(k: K)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures AddModel(k)

    opaque twostate predicate RemoveModel(k: K)
      reads Repr()
      requires old(Valid())
      requires Valid()
    {
      && Model() == old(Model()) - {k}
      && if k in old(Model()) then
        |Model()| == old(|Model()|) - 1
      else
        |Model()| == old(|Model()|)
    }

    method Remove(k: K)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Iterators() >= old(Iterators())
      ensures RemoveModel(k)

    opaque twostate predicate FindModel(k: K, new it: OrderedSetIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires it.Valid()
      requires it.Parent() == this
    {
      && Model() == old(Model())
      && |Model()| == old(|Model()|)
      && it.HasPeek?() == (k in old(Model()))
      && if k in old(Model()) then
        it.Peek?() == k
      else
        it.PastTheEnd?()
    }

    method Find(k: K) returns (it: OrderedSetIterator)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()

      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures Iterators() >= {it}+old(Iterators())

      ensures FindModel(k, it)

    opaque twostate predicate InsertModel(k: K, new it: OrderedSetIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires it.Valid()
      requires it.Parent() == this
      requires it.HasPeek?()
    {
      && Model() == old(Model()) + {k}
      && (
        if k in old(Model()) then
          |Model()| == old(|Model()|)
        else
          |Model()| == old(|Model()|) + 1
      )
      && it.Peek?() == k
    }

    method Insert(hint: OrderedSetIterator, k: K) returns (it: OrderedSetIterator)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires hint.Valid()
      requires hint.Parent() == this
      requires hint in Iterators()

      ensures Valid()
      ensures fresh(it)
      ensures it.Valid() && it.Parent() == this
      ensures it.HasPeek?()
      ensures Iterators() >= {it} + old(Iterators())
      ensures InsertModel(k, it)

    opaque twostate predicate EraseModel(pos: OrderedSetIterator, new it: OrderedSetIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires old(pos.Valid())
      requires pos.Parent() == this
      requires old(pos.HasPeek?())
      requires it.Valid()
      requires it.Parent() == this
    {
      && Model() == old(Model()) - {old(pos.Peek?())}
      && |Model()| == old(|Model()|) - 1
      //&& old(pos.Peek?()) in old(Model())
      && it.Before'() == old(pos.Before())
      && |it.Before'()| == old(|pos.Before()|)
    }

    opaque twostate predicate EraseIteratorModel(it: OrderedSetIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires it.Valid()
      requires it.HasPeek?() == old(it.HasPeek?())
    {
      true
      /*
      && it.Before'() == old(it.Before'())
      && |it.Before'()| == old(|it.Before'()|)
      && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
      */
    }

    opaque twostate predicate EraseIterators(pos: OrderedSetIterator)
      reads Repr()
      requires old(Valid())
      requires Valid()
      requires Iterators() >= old(Iterators())
      requires old(pos.Valid())
      requires old(pos.HasPeek?())
    {
      var x := old(pos.Peek?());
      assert old(Allocated(Repr()); true);  // am I breaking something?
      forall it <- old(Iterators()) |
          && old(it.Valid())
          && (old(it.HasPeek?()) ==> old(it.Peek?()) != x) ::
        && it.Valid()
        && it.HasPeek?() == old(it.HasPeek?())
        && EraseIteratorModel(it)
        //&& it.Parent() == old(it.Parent())
    }

    twostate lemma EraseIteratorNHP(pos: OrderedSetIterator, it: OrderedSetIterator)
      requires old(Valid())
      requires Valid()
      requires old(pos.Valid())
      requires old(pos.HasPeek?())
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(!it.HasPeek?())
      requires EraseIterators(pos)
      ensures it.Valid()
      ensures !it.HasPeek?()
      ensures EraseIteratorModel(it)
    {
      reveal EraseIterators();
    }

    twostate lemma EraseIteratorHP(pos: OrderedSetIterator, it: OrderedSetIterator)
      requires old(Valid())
      requires Valid()
      requires old(pos.Valid())
      requires old(pos.HasPeek?())
      requires Iterators() >= old(Iterators())
      requires it in old(Iterators())
      requires old(it.Valid())
      requires old(it.HasPeek?())
      requires old(it.Peek?() != pos.Peek?())
      requires EraseIterators(pos)
      ensures it.Valid()
      ensures it.HasPeek?()
      ensures EraseIteratorModel(it)
    {
      reveal EraseIterators();
    }

    method Erase(pos: OrderedSetIterator) returns (it: OrderedSetIterator)
      modifies Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires pos.Valid()
      requires pos.Parent() == this
      requires pos.HasPeek?()
      requires pos in Iterators()

      ensures Valid()
      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures Iterators() >= {it} + old(Iterators())
      ensures EraseModel(pos, it)
      ensures EraseIterators(pos)
  }

  datatype OrdSetIt = OrdSetIt(s: OrderedSet, it: OrderedSetIterator)
  {
    ghost predicate Valid()
      reads s, s.Repr()
      requires s.Valid()
    {
      && it.Parent() == s
      && it in s.Iterators()
      && it.Valid()
    }
  }

  datatype OrdSet2It11 = OrdSet2It11(
    a: OrderedSet,
    itA: OrderedSetIterator,
    b: OrderedSet,
    itB: OrderedSetIterator
  ) {
    ghost predicate Valid()
      reads a, a.Repr(), b, b.Repr()
    {
      && ADT2(a, b).Valid()
      && OrdSetIt(a, itA).Valid()
      && OrdSetIt(b, itB).Valid()
    }
  }

  datatype OrdSet3It110 = OrdSet3It110(
    a: OrderedSet,
    itA: OrderedSetIterator,
    b: OrderedSet,
    itB: OrderedSetIterator,
    c: OrderedSet
  ) {
    ghost function Repr(): set<object>
      reads a, a.ReprFamily(a.ReprDepth-1)
      reads b, b.ReprFamily(b.ReprDepth-1)
      reads c, c.ReprFamily(c.ReprDepth-1)
    {
      ADT3(a, b, c).Repr()
    }

    ghost predicate {:inline} Valid()
      reads a, a.Repr(), b, b.Repr(), c, c.Repr()
    {
      && ADT3(a, b, c).Valid()
      && OrdSetIt(a, itA).Valid()
      && OrdSetIt(b, itB).Valid()
    }
  }

  ghost predicate ValidIt(s: OrderedSet, it: OrderedSetIterator)
    reads s, s.Repr()
    requires s.Valid()
  {
    && it.Parent() == s
    && it in s.Iterators()
    && it.Valid()
  }

  ghost predicate Valid2It11(
      a: OrderedSet,
      itA: OrderedSetIterator,
      b: OrderedSet,
      itB: OrderedSetIterator
    )
    reads a, a.Repr(), b, b.Repr()
  {
    && Valid2(a, b)
    && ValidIt(a, itA)
    && ValidIt(b, itB)
  }

  twostate predicate MaintainsValid2It11(
      a: OrderedSet,
      itA: OrderedSetIterator,
      b: OrderedSet,
      itB: OrderedSetIterator
    )
    reads a, a.Repr(), b, b.Repr()
    requires old(Valid2It11(a, itA, b, itB))
  {
    && Valid2It11(a, itA, b, itB)
    && MaintainsValid2(a, b)
    && a.Iterators() >= old(a.Iterators())
    && b.Iterators() >= old(b.Iterators())
  }

  twostate lemma MaintainsValid2It11Helper(
      a: OrderedSet,
      itA: OrderedSetIterator,
      b: OrderedSet,
      itB: OrderedSetIterator
    )
    requires old(Valid2It11(a, itA, b, itB))

    requires a.Valid()
    requires ValidIt(a, itA)
    requires fresh(a.Repr() - old(a.Repr()))
    requires a.Iterators() >= old(a.Iterators())

    requires old(allocated(a.Repr()))
    requires old(allocated(b.Repr()))
    requires allocated(b.Repr())
    requires b.Repr() == old(b.Repr())
    requires unchanged({b} + b.Repr())

    ensures MaintainsValid2It11(a, itA, b, itB)
    ensures allocated(a.Repr())
    ensures allocated(b.Repr())
  {}

  ghost predicate Valid3It110(
      a: OrderedSet,
      itA: OrderedSetIterator,
      b: OrderedSet,
      itB: OrderedSetIterator,
      c: OrderedSet
    )
    reads a, a.Repr(), b, b.Repr(), c, c.Repr()
  {
    && Valid3(a, b, c)
    && ValidIt(a, itA)
    && ValidIt(b, itB)
  }

  twostate lemma MaintainsValid3It110Helper(
      a: OrderedSet,
      itA: OrderedSetIterator,
      b: OrderedSet,
      itB: OrderedSetIterator,
      c: OrderedSet
    )
    requires old(Valid3It110(a, itA, b, itB, c))

    requires a.Valid()
    requires ValidIt(a, itA)
    requires fresh(a.Repr() - old(a.Repr()))
    requires a.Iterators() >= old(a.Iterators())

    requires old(allocated(a.Repr()))
    requires old(allocated(b.Repr()))
    requires old(allocated(c.Repr()))
    requires allocated(b.Repr())
    requires allocated(c.Repr())
    requires b.Repr() == old(b.Repr())
    requires c.Repr() == old(c.Repr())
    requires unchanged(b.Repr())
    requires unchanged(c.Repr())

    ensures Valid3It110(a, itA, b, itB, c)
    ensures fresh(a.Repr() - old(a.Repr()))
    ensures fresh(b.Repr() - old(b.Repr()))
    ensures fresh(c.Repr() - old(c.Repr()))
    ensures a.Iterators() >= old(a.Iterators())
    ensures b.Iterators() >= old(b.Iterators())
    ensures c.Iterators() >= old(c.Iterators())
    ensures allocated(a.Repr())
    ensures allocated(b.Repr())
    ensures allocated(c.Repr())
  {}

  ghost predicate ValidIt2(
      a: OrderedSet,
      itA: OrderedSetIterator,
      itB: OrderedSetIterator
    )
    reads a, a.Repr()
  {
    && a.Valid()
    && ValidIt(a, itA)
    && ValidIt(a, itB)
  }

  opaque twostate predicate Loop'Model(
      s1: OrderedSet, 
      it1: OrderedSetIterator, 
      s2: OrderedSet, 
      it2: OrderedSetIterator, 
      su: OrderedSet
    )
    reads s1, s1.Repr(), s2, s2.Repr(), su, su.Repr()
    requires old(Valid3It110(s1, it1, s2, it2, su))
    requires old(it1.HasPeek?())
    requires old(it2.HasPeek?())
    requires Valid3It110(s1, it1, s2, it2, su)
  {
    var x := old(it1.Peek?());
    var y := old(it2.Peek?());
    && s1.Model() == old(s1.Model())
    && s2.Model() == old(s2.Model())
    && !it1.PastTheBeginning?()
    && !it2.PastTheBeginning?()
    && (
      if x == y then
        && su.Model() == old(su.Model()) + {x}
        && it1.Before'() == old(it1.Before()) + {x}
        && it2.Before'() == old(it2.Before()) + {y}
      else if x < y then
        && su.Model() == old(su.Model())
        && it1.Before'() == old(it1.Before()) + {x}
        && it2.Before'() == old(it2.Before())
      else
        && su.Model() == old(su.Model())
        && it1.Before'() == old(it1.Before())
        && it2.Before'() == old(it2.Before()) + {y}
    )
  }

  // 5.07M RU - correctness verification (with MaintainsValid..., without "reads/modifies this"))
  method {:only} Loop'(
      s1: OrderedSet, 
      it1: OrderedSetIterator, 
      s2: OrderedSet, 
      it2: OrderedSetIterator, 
      su: OrderedSet
    )
    returns (
      it1HasPeek: bool,
      it2HasPeek: bool
    )
    modifies s1.Repr(), s2.Repr(), su.Repr()
    requires allocated(s1.Repr())
    requires allocated(s2.Repr())
    requires allocated(su.Repr())
    ensures allocated(s1.Repr())
    ensures allocated(s2.Repr())
    ensures allocated(su.Repr())
    ensures fresh(s1.Repr()-old(s1.Repr()))
    ensures fresh(s2.Repr()-old(s2.Repr()))
    ensures fresh(su.Repr()-old(su.Repr()))

    requires Valid3It110(s1, it1, s2, it2, su)
    requires it1.HasPeek?()
    requires it2.HasPeek?()
    ensures Valid3It110(s1, it1, s2, it2, su)
    ensures it1HasPeek <==> it1.HasPeek?()
    ensures it2HasPeek <==> it2.HasPeek?()
    ensures Loop'Model(s1, it1, s2, it2, su)

    ensures s1.Iterators() >= old(s1.Iterators())
    ensures s2.Iterators() >= old(s2.Iterators())
    ensures su.Iterators() >= old(su.Iterators())
  {
    var it1Peek := it1.Peek();
    MaintainsValid3It110Helper(s1, it1, s2, it2, su);
    label L1:
    var it2Peek := it2.Peek();
    MaintainsValid3It110Helper@L1(s2, it2, s1, it1, su);
    if it1Peek == it2Peek {
      label L2:
      su.Add(it1Peek); 
      MaintainsValid3Helper@L2(su, s2, s1);
      label L3:
      it1.Next();
      MaintainsValid3It110Helper@L3(s1, it1, s2, it2, su);
      label L4:
      it2.Next();
      MaintainsValid3It110Helper@L4(s2, it2, s1, it1, su);
    } else if it1Peek < it2Peek {
      label L7:
      it1.Next();
      MaintainsValid3It110Helper@L7(s1, it1, s2, it2, su);
    } else {
      label L10:
      it2.Next();
      MaintainsValid3It110Helper@L10(s2, it2, s1, it1, su);
    }
    assert Valid3It110(s1, it1, s2, it2, su);
    label L5:
    it1HasPeek := it1.HasPeek();
    MaintainsValid3It110Helper@L5(s1, it1, s2, it2, su);
    label L6:
    it2HasPeek := it2.HasPeek();
    MaintainsValid3It110Helper@L6(s2, it2, s1, it1, su);
    assert Loop'Model(s1, it1, s2, it2, su) by {
      assume false;
      reveal Loop'Model();
      reveal it1.PeekModel(), it2.PeekModel(), su.AddModel(), it1.NextModel(), it2.NextModel();
      reveal it1.HasPeekModel();
      reveal it2.HasPeekModel();
    }
  }
}
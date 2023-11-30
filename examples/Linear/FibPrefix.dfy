include "../../src/Collections/Set.dfy"
include "../../src/List/ListSpec.dfy"
include "../../src/LinkedList/LinkedListImpl.dfy"

module FibPrefix {
  import Set
  import opened ListSpec
  import opened LinkedListImpl

  /*
    Standard definition of Fibonacci function
  */
  ghost function Fib(n: nat): nat
  {
    if n == 0 then 0
    else if n == 1 then 1
    else Fib(n - 1) + Fib(n - 2)
  }

  /*
    Given a number `n`, it returns the sequence [Fib(0), Fib(1), ..., Fib(n)]
    This sequence has `n + 1` elements
  */
  ghost function FibSeq(n: nat): seq<nat>
  {
    seq(n + 1, (i:nat) => Fib(i))
  }

  /*
    Function for obtaining a copy of a list. It uses iterators
  */
  method Copy<A>(l: List<A>) returns (nl: List<A>)  // 10s
    modifies l, l.Repr()
    requires l.Valid()
    requires allocated(l.Repr())

    ensures allocated(l.Repr())
    ensures allocated(nl.Repr())
    ensures fresh(l.Repr() - old(l.Repr()))
    ensures fresh(nl)
    ensures fresh(nl.Repr())
    ensures ({l} + l.Repr()) !! ({nl} + nl.Repr())

    ensures l.Valid() && nl.Valid() 
    ensures l.Model() == old(l.Model())
    ensures nl.Model() == l.Model()
  {
    nl := new LinkedListImpl();
    var it := l.First();
    var b := it.HasPeek();
    while b
      decreases |l.Model()| - it.Index()
      invariant allocated(l.Repr())
      invariant allocated(nl.Repr())
      invariant fresh(l.Repr() - old(l.Repr()))
      invariant fresh(nl)
      invariant fresh(nl.Repr())
      invariant ({l} + l.Repr()) !! ({nl} + nl.Repr())

      invariant l.Valid() && nl.Valid() 
      invariant it.Valid()
      invariant it.Parent() == l
      invariant b == it.HasPeek?()

      invariant l.Model() == old(l.Model())
      invariant 0 <= it.Index() <= |old(l.Model())|
      invariant nl.Model() == l.Model()[..it.Index()]
    {
      var x := it.Peek();
      it.Next();
      nl.PushBack(x);
      b := it.HasPeek();
    }
  }

/*
  // This is a recursive version of the method above.
  // It does the same, but with faster verification times (2s)

  method Copy<A>(l: List<A>) returns (res: List<A>)
    requires allocated({l} + l.Repr())
    requires l.Valid()

    modifies l, l.Repr()

    ensures l.Valid()
    ensures allocated({l} + l.Repr())
    ensures fresh(l.Repr() - old(l.Repr()))
    ensures l.Model() == old(l.Model())

    ensures res.Valid()
    ensures allocated({res} + res.Repr())
    ensures fresh(res) && fresh(res.Repr())

    ensures ({res} + res.Repr()) !! ({l} + l.Repr())

    ensures res.Model() == l.Model()
  {
    res := new LinkedListImpl<A>();
    var it := l.First();
    CopyAux(l, it, res);
  }

  method CopyAux<A>(l: List<A>, it: ListIterator<A>, res: List<A>)
    requires allocated({l} + l.Repr())
    requires l.Valid()

    requires ({l} + l.Repr()) !! ({res} + res.Repr())

    requires allocated({res} + res.Repr())
    requires res.Valid()

    requires allocated(it)
    requires it.Valid()
    requires it.Parent() == l
    requires 0 <= it.Index() <= |l.Model()|

    requires res.Model() == l.Model()[..it.Index()]


    modifies l, l.Repr()
    modifies res, res.Repr()
    modifies it

    decreases |l.Model()| - it.Index()

    ensures allocated({l} + l.Repr())
    ensures l.Valid()
    ensures fresh(l.Repr() - old(l.Repr()))
    ensures l.Model() == old(l.Model())

    ensures allocated({res} + res.Repr())
    ensures res.Valid()
    ensures fresh(res.Repr() - old(res.Repr()))
    ensures res.Model() == l.Model()

    ensures ({l} + l.Repr()) !! ({res} + res.Repr())
  {
    var b := it.HasPeek();
    if b {
      var elem := it.Peek();
      res.PushBack(elem);
      it.Next();
      CopyAux(l, it, res);
    }
  }
*/

  /*
    Invariant relative to the inner lists:
      - All their models are valid
      - Their footprints are disjoint from outer list's footprint
      - Their footprints are disjoint to each other
  */
  ghost predicate InnerListsValid<A>(xss: List<List<A>>)
    requires xss.Valid()
    reads xss, xss.Repr(), set i | 0 <= i < |xss.Model()| :: xss.Model()[i],
        Set.BigUnion(set i | 0 <= i < |xss.Model()| :: xss.Model()[i].Repr())
  {
    (forall i | 0 <= i < |xss.Model()| :: xss.Model()[i].Valid())
    && (forall i | 0 <= i < |xss.Model()| :: ({xss} + xss.Repr()) !! ({xss.Model()[i]} + xss.Model()[i].Repr()))
    && (forall i, j | 0 <= i < j < |xss.Model()|
      :: ({xss.Model()[i]} + xss.Model()[i].Repr()) !! ({xss.Model()[j]} + xss.Model()[j].Repr()))
  }


  /*
    Assume that `xss` a list of lists that satisfies InnerListsValid(xss)

    If the footprint of the idx-th inner list has grown with fresh cells, but
    the others stay the same, then `xss` still satisfies InnerListsValid(xss)
  */
  twostate lemma IndexChanged<A>(xss: List<List<A>>, idx: nat)
    // Assume the list was valid and allocated
    requires old(allocated({xss} + xss.Repr()))
    requires old(xss.Valid())
    requires forall i | 0 <= i < old(|xss.Model()|) :: old(allocated(xss.Model()[i]))
    requires forall i | 0 <= i < old(|xss.Model()|) :: old(allocated(xss.Model()[i].Repr()))
    requires old(InnerListsValid(xss))

    // Assume that the outer list is still valid, its model hasn't changed, and neither has its footprint
    requires xss.Valid()
    requires xss.Model() == old(xss.Model())
    requires xss.Repr() == old(xss.Repr())

    // Assume that the inner list we have changed (i.e., that in the idx-th position) is still valid
    requires 0 <= idx < |xss.Model()|
    requires xss.Model()[idx].Valid()
    requires fresh(xss.Model()[idx].Repr() - old(xss.Model()[idx].Repr()))

    // Assume that the other inner lists haven't changed
    requires forall i | 0 <= i < |xss.Model()| && i != idx 
      :: xss.Model()[i].Repr() == old(xss.Model()[i].Repr())
    requires forall i | 0 <= i < |xss.Model()| && i != idx :: unchanged(xss.Model()[i])
    requires forall i | 0 <= i < |xss.Model()| && i != idx :: unchanged(xss.Model()[i].Repr())

    // THEN: all the inner lists are still valid and disjoint
    ensures allocated({xss} + xss.Repr())
    ensures forall i | 0 <= i < |xss.Model()| :: allocated(xss.Model()[i])
    ensures forall i | 0 <= i < |xss.Model()| :: allocated(xss.Model()[i].Repr())
    ensures InnerListsValid(xss)
  { }

  /*
    Assume that `xss` a list of lists that satisfies InnerListsValid(xss)

    If we add a new list `addedElement` to `xss`, and that list is disjoint from the
    already existing ones (and from the outer list itself), then the result still
    satisfies InnerListsVald(xss)
  */

  twostate lemma OuterListAddedElement<A>(xss: List<List<A>>, addedElement: List<A>)
    // Assume the list was valid and allocated
    requires old(xss.Valid())
    requires old(InnerListsValid(xss))
    requires old(allocated({xss} + xss.Repr()))
    requires forall i | 0 <= i < old(|xss.Model()|) :: old(allocated(xss.Model()[i]))
    requires forall i | 0 <= i < old(|xss.Model()|) :: old(allocated(xss.Model()[i].Repr()))

    // Assume the list is still valid, allocated, and its representation has grown with
    // the new element
    requires xss.Valid()
    requires allocated({xss} + xss.Repr())
    requires fresh(xss.Repr() - old(xss.Repr()))
    requires xss.Model() == old(xss.Model()) + [addedElement]

    // Assume that the new list is disjoint from the outer list
    requires ({addedElement} + addedElement.Repr()) !! ({xss} + xss.Repr())
    // ..and is also disjoint from the already existing inner lists
    requires forall i | 0 <= i < old(|xss.Model()|) ::
        (old({xss.Model()[i]} + xss.Model()[i].Repr())) !! ({addedElement} + addedElement.Repr())
    // And, of course, that the new list is valid
    requires addedElement.Valid()

    // We assume that the already existing lists haven't changed
    requires forall i | 0 <= i < old(|xss.Model()|) :: xss.Model()[i].Repr() == old(xss.Model()[i].Repr())
    requires forall i | 0 <= i < old(|xss.Model()|) :: unchanged(xss.Model()[i])
    requires forall i | 0 <= i < old(|xss.Model()|) :: unchanged(xss.Model()[i].Repr())

    // THEN: all the inner lists are still valid and disjoint after the addition
    ensures allocated({xss} + xss.Repr())
    ensures forall i | 0 <= i < |xss.Model()| :: allocated(xss.Model()[i])
    ensures forall i | 0 <= i < |xss.Model()| :: allocated(xss.Model()[i].Repr())
    ensures InnerListsValid(xss)
  { }


  /*
    Given a list of lists, it returns whether its model is
    [
     [Fib(0)],
     [Fib(0), Fib(1)],
     [Fib(0), Fib(1), Fib(2)],
     ...
     [Fib(0), Fib(1), Fib(2), ..., Fib(n)],
    ]
  */
  ghost predicate IsFibPyramid(xss: List<List<int>>, n: nat)
    reads xss, xss.Repr(), set i | 0 <= i < |xss.Model()| :: xss.Model()[i],
      Set.BigUnion(set i | 0 <= i < |xss.Model()| :: xss.Model()[i].Repr())
    requires xss.Valid()
    requires InnerListsValid(xss)
  {
    |xss.Model()| == n + 1
    && forall i | 0 <= i < |xss.Model()| :: xss.Model()[i].Model() == FibSeq(i)
  }
 


  /*
    Given a list `xs`, it returns its last element (`last`) and its
    last-but-one element (`previous`).
  */
  method GetTwoLast<A>(xs: List<A>) returns (last: A, previous: A)
    requires xs.Valid()
    requires allocated(xs) && allocated(xs.Repr())
    requires |xs.Model()| > 1
    
    modifies xs, xs.Repr()
    
    ensures xs.Valid()
    ensures allocated(xs) && allocated(xs.Repr())
    ensures fresh(xs.Repr() - old(xs.Repr()))
    ensures xs.Model() == old(xs.Model())

    ensures last == xs.Model()[|xs.Model()| - 1]
    ensures previous == xs.Model()[|xs.Model()| - 2] 
  {
    last := xs.PopBack();
    previous := xs.Back();
    xs.PushBack(last);
  }


  /*
    Given a list `xs` and an element `x`, it returns a freshly generated
    list whose model is `xs + [x]`.
  */
  method BuildNewList<A>(xs: List<A>, x: A) returns (newXs: List<A>)
    requires xs.Valid()
    requires allocated(xs) && allocated(xs.Repr())

    modifies xs, xs.Repr()

    ensures xs.Valid()
    ensures allocated(xs) && allocated(xs.Repr())
    ensures fresh(xs.Repr() - old(xs.Repr()))
    ensures xs.Model() == old(xs.Model())

    ensures newXs.Valid()
    ensures allocated(newXs) && allocated(newXs.Repr())
    ensures fresh(newXs) && fresh(newXs.Repr())
    ensures newXs.Model() == xs.Model() + [x]

    // We have said, the footprint of `xs` may grow with fresh cells, but that doesn't
    // prevent some of these fresh cells from being those of `newXs`, unless
    // we explicitly say that `xs` and `newXs` are separated.
    ensures ({newXs} + newXs.Repr()) !! ({xs} + xs.Repr())
  {
    newXs := Copy(xs);
    newXs.PushBack(x);
  }


  /*
    Given a list of lists which makes up a FibPyramid of length n, modify it
    such that their elements make up a FibPyramid of length n+1.

    It returns the freshly generated row as a ghost result, but this is just
    to make specification simpler; it is not used actually.
  */
  method AddOneRow(xss: List<List<int>>) returns (ghost newRow: List<int>)
    // The list of lists is valid and allocated
    requires xss.Valid()
    requires allocated({xss} + xss.Repr())
    requires forall xs | xs in xss.Model() :: allocated({xs} + xs.Repr())
    requires InnerListsValid(xss)

    // xss is actually a FibPyramid with at least two inner lists, so that
    // the last list contains, at least, two elements
    requires |xss.Model()| >= 2
    requires IsFibPyramid(xss, |xss.Model()| - 1)
    
    modifies xss, xss.Repr(), set i | 0 <= i < |xss.Model()| :: xss.Model()[i],
            Set.BigUnion(set i | 0 <= i < |xss.Model()| :: xss.Model()[i].Repr())
    
    // `xss` is valid after updating it
    ensures xss.Valid()
    ensures allocated({xss} + xss.Repr())
    ensures fresh(xss.Repr() - old(xss.Repr()))
    ensures InnerListsValid(xss)


    // `xss` has a new element, which is also valid, and `xss` is still a FibPyramid
    ensures xss.Model() == old(xss.Model()) + [newRow]
    ensures newRow.Valid()
    ensures fresh(newRow) && fresh(newRow.Repr())
    ensures IsFibPyramid(xss, |xss.Model()| - 1)

    // The footprint of the remaining lists may have grown, but only with fresh cells
    ensures forall xs | xs in xss.Model() :: allocated({xs} + xs.Repr())
    ensures forall i | 0 <= i < old(|xss.Model()|) :: fresh(xss.Model()[i].Repr() - old(xss.Model()[i].Repr()))

  {
    ghost var n := |xss.Model()|;
    var inner := xss.Back();
    assert inner.Model() == FibSeq(n - 1);
    assert InnerListsValid(xss);
  label L1:
    var last, previous := GetTwoLast(inner);
    // The last inner sublist may have changed, but we ensure that `xss`
    // is still ok
    IndexChanged@L1(xss, |xss.Model()| - 1);
    assert xss.Valid() && InnerListsValid(xss);
    assert last == Fib(n - 1);
    assert previous == Fib(n - 2);
    assert IsFibPyramid(xss, n - 1);

  label L2:
    var newList := BuildNewList(inner, last + previous);
    // The last inner sublist may have changed, but we ensure that `xss`
    // is still ok
    IndexChanged@L2(xss, |xss.Model()| - 1);
    assert xss.Valid() && InnerListsValid(xss);
    assert last + previous == Fib(n);
    assert newList.Model() == inner.Model() + [Fib(n)];
    assert newList.Model() == FibSeq(n);
    assert IsFibPyramid(xss, n - 1);

  label L3:
    xss.PushBack(newList);
    // We have added an element, but we ensure that `xss` is still ok.
    OuterListAddedElement@L3(xss, newList);
    assert xss.Valid() && InnerListsValid(xss);
    assert IsFibPyramid(xss, n);
    
    newRow := newList;
  }


  /*
    Given a list of lists [[Fib(0)], [Fib(0), Fib(1)]], it adds new rows
    until `xss` becomes a FibPyramid of length `n + 1`
  */
  method FibPrefixesLoop(xss: List<List<int>>, n: nat)
    requires n >= 1

    // Assume that `xss` is valid and their inner lists disjoint
    requires xss.Valid()
    requires allocated({xss} + xss.Repr())
    requires forall xs | xs in xss.Model() :: allocated({xs} + xs.Repr())
    requires InnerListsValid(xss)

    // Assume that `xss` denotes the list [[Fib(0)], [Fib(0), Fib(1)]]
    requires IsFibPyramid(xss, 1)
    
    modifies xss, xss.Repr(), set i | 0 <= i < |xss.Model()| :: xss.Model()[i],
            Set.BigUnion(set i | 0 <= i < |xss.Model()| :: xss.Model()[i].Repr())

    // Then, `xss` is still valid and their inner lists disjoint
    ensures xss.Valid()
    ensures allocated({xss} + xss.Repr())
    ensures fresh(xss.Repr() - old(xss.Repr()))
    ensures InnerListsValid(xss)
    ensures forall i | 0 <= i < |xss.Model()| :: allocated({xss.Model()[i]} + xss.Model()[i].Repr())

    // `xss` has more elements than before
    ensures |xss.Model()| >= old(|xss.Model()|)


    // The already existing sublists haven't changed, and if their representation has grown, it has grown
    // only with fresh cells
    ensures forall i | 0 <= i < old(|xss.Model()|) :: xss.Model()[i] == old(xss.Model()[i])
    ensures forall i | 0 <= i < old(|xss.Model()|) :: fresh(xss.Model()[i].Repr() - old(xss.Model()[i].Repr()))
    // The newly added sublists are fresh
    ensures forall i | old(|xss.Model()|) <= i < |xss.Model()| :: fresh(xss.Model()[i])
    ensures forall i | old(|xss.Model()|) <= i < |xss.Model()| :: fresh(xss.Model()[i].Repr())

    // And the result is a FibPyramid of length `n + 1`
    ensures IsFibPyramid(xss, n)
  {
    var j := 1;
    while j < n
      invariant 1 <= j <= n
      invariant allocated({xss} + xss.Repr())
      invariant fresh(xss.Repr() - old(xss.Repr()))

      invariant xss.Valid() && !xss.Empty?()
      invariant InnerListsValid(xss)
      invariant |xss.Model()[|xss.Model()| - 1].Model()| > 1
      invariant |xss.Model()| >= old(|xss.Model()|)
      invariant forall i | 0 <= i < old(|xss.Model()|) :: xss.Model()[i] == old(xss.Model()[i])
      invariant forall i | 0 <= i < old(|xss.Model()|) :: fresh(xss.Model()[i].Repr() - old(xss.Model()[i].Repr()))
      invariant forall i | old(|xss.Model()|) <= i < |xss.Model()| :: fresh(xss.Model()[i])
      invariant forall i | 0 <= i < |xss.Model()| :: allocated({xss.Model()[i]} + xss.Model()[i].Repr())
      invariant forall i | old(|xss.Model()|) <= i < |xss.Model()| :: fresh(xss.Model()[i].Repr())
      invariant IsFibPyramid(xss, j)
    {
      ghost var newRow := AddOneRow(xss);
      j := j + 1;
    }
  }

  /*
    It returns the list [0]
  */
  method CreateZeroList() returns (xs: List<int>)
    ensures xs.Valid()
    ensures xs.Model() == [0]
    ensures allocated(xs) && allocated(xs.Repr())
    ensures fresh(xs) && fresh(xs.Repr())
  {
    xs := new LinkedListImpl();
    xs.PushBack(0);
  }

  /*
    It returns the list [0, 1]
  */
  method CreateZeroOneList() returns (xs: List<int>)
    ensures xs.Valid()
    ensures xs.Model() == [0, 1]
    ensures allocated(xs) && allocated(xs.Repr())
    ensures fresh(xs) && fresh(xs.Repr())
  {
    xs := new LinkedListImpl();
    xs.PushBack(0);
    xs.PushBack(1);
  }


  /*
    It returns the list [[Fib(0)], [Fib(0), Fib(1)]]
  */
  method FibPrefixesBase() returns (xss: List<List<int>>)
    ensures xss.Valid()
    ensures !xss.Empty?()
    ensures allocated({xss} + xss.Repr())
    ensures fresh({xss} + xss.Repr())
    ensures InnerListsValid(xss)
    ensures forall i | 0 <= i < |xss.Model()| :: allocated({xss.Model()[i]} + xss.Model()[i].Repr())
    ensures forall i | 0 <= i < |xss.Model()| :: fresh(xss.Model()[i]) && fresh(xss.Model()[i].Repr())
    ensures IsFibPyramid(xss, 1)
  {
    xss := new LinkedListImpl();
    var inner0 := CreateZeroList();
  label L1:
    xss.PushBack(inner0);
    OuterListAddedElement@L1(xss, inner0);

    var inner1 := CreateZeroOneList();
  label L2:
    xss.PushBack(inner1);
    OuterListAddedElement@L2(xss, inner1);
  }

  /*
    Given a number n, it returns a list `xss` which
    is a FibPyramid of length `n + 1`.
  */
  method FibPrefix(n: nat) returns (xss: List<List<int>>)
    requires n >= 1
    ensures allocated({xss} + xss.Repr())
    ensures fresh({xss} + xss.Repr())
    ensures xss.Valid()
    ensures InnerListsValid(xss)
    ensures forall i | 0 <= i < |xss.Model()| :: allocated({xss.Model()[i]} + xss.Model()[i].Repr())
    ensures forall i | 0 <= i < |xss.Model()| :: fresh({xss.Model()[i]} + xss.Model()[i].Repr())
    ensures IsFibPyramid(xss, n)
  {
    xss := FibPrefixesBase();
    FibPrefixesLoop(xss, n);
  }
  
}

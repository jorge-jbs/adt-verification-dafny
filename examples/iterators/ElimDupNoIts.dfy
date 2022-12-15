include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"
include "../../src/Order.dfy"

predicate Sorted<A>(xs: seq<A>,le:(A,A)->bool)
requires IsTotalOrder(le)
{
  forall i, j :: 0 <= i <= j < |xs| ==> le(xs[i],xs[j])
}

predicate StrictSorted<A>(xs: seq<A>,le:(A,A)->bool)
requires IsTotalOrder(le)
{
  forall i, j :: 0 <= i < j < |xs| ==> (le(xs[i],xs[j]) && !le(xs[j],xs[i])) 
}

method ElimDup<A>(l:List<A>,le:(A,A)->bool)
//method {:verify true} elimDupA(l:ArrayList<int>) //NO CHANGES
 modifies l, l.Repr()
 requires allocated(l.Repr())
 ensures fresh(l.Repr()-old(l.Repr()))
 ensures allocated(l.Repr())
 requires IsTotalOrder(le)

 requires l.Valid() && Sorted(l.Model(),le)
 ensures l.Valid()

 ensures (set x | x in old(l.Model())) == (set x | x in l.Model())
 ensures StrictSorted(l.Model(),le)

 ensures l.Iterators() >= old(l.Iterators())
{
  var it2 := l.First();
  var it1 := it2.Copy();
  var b := it1.HasPeek();

  if (b) {
    it2.Next();

    ghost var j := 1;
    assert it2.HasPeek?() ==> it1.HasPeek?() && l.Model()[it1.Index()+1] == l.Model()[it2.Index()];
    assert it2.Index() == 1 && it1.Index() == 0;

    ghost var omodel := l.Model();
    b := it2.HasPeek();

    while b
      decreases |l.Model()| - it2.Index()
      invariant allocated(l.Repr())
      invariant fresh(l.Repr()-old(l.Repr()))

      invariant l.Valid()
      invariant it2 in l.Iterators() && it1 in l.Iterators()
      invariant it1.Parent() == l && it2.Parent() == l
      invariant it1.Valid() && it2.Valid()
      invariant it1.Index() >= 0
      invariant it2.Index() == it1.Index()+1
      invariant it2.HasPeek?() ==> it1.HasPeek?() && l.Model()[it1.Index()+1] == l.Model()[it2.Index()]

      invariant (set x | x in old(l.Model())) == (set x | x in l.Model())
      invariant Sorted(l.Model(),le) && StrictSorted(l.Model()[..it2.Index()],le)
      invariant b == it2.HasPeek?()

      invariant l.Iterators() >= old(l.Iterators())
    {
     var it1Peek := it1.Peek();
     var it2Peek := it2.Peek();
     if (le(it1Peek,it2Peek) && le(it2Peek,it1Peek)) 
     {
        assert it1Peek == it2Peek;
        ghost var oit2 := it2.Index();
        it2 := l.Erase(it2);
      } else {
        it2.Next();
        it1.Next();
      }
      j := j+1;
      b:=it2.HasPeek();  
    }
  }

}

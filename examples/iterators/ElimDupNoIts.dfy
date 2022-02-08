include "../../src/linear/layer1/List.dfy"
include "../../src/linear/layer2/LinkedList.dfy"
include "../../src/linear/layer2/ArrayList.dfy"
include "../../src/UtilsAux.dfy"

method elimDup(l:LinkedList)
//method {:verify true} elimDupA(l:ArrayList) //NO CHANGES

 modifies l, l.Repr()
 requires l.Valid() && Sorted(l.Model())
 requires forall x | x in l.Repr() :: allocated(x)
 ensures l.Valid()

 ensures (set x | x in old(l.Model())) == (set x | x in l.Model())
 ensures StrictSorted(l.Model())

 ensures l.Iterators() >= old(l.Iterators())

 ensures forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
 ensures fresh(l.Repr()-old(l.Repr()))
 ensures forall x | x in l.Repr() :: allocated(x)
{
  var aux;
  var it2 := l.Begin();
  var it1 := it2.Copy();
  if (it1.HasNext()) {
    aux := it2.Next();

    ghost var j := 1;
    assert it2.HasNext() ==> it1.HasNext() && l.Model()[it1.Index()+1]==l.Model()[it2.Index()];
    assert it2.Index()==1 && it1.Index()==0;

    ghost var omodel := l.Model();

    while (it2.HasNext())
      decreases |l.Model()| - it2.Index()
      invariant l.Valid()
      invariant it2 in l.Iterators() && it1 in l.Iterators()
      invariant it1.Parent() == l && it2.Parent()==l
      invariant it1.Valid() && it2.Valid()
      invariant it2.Index()==it1.Index()+1
      invariant it2.HasNext() ==> it1.HasNext() && l.Model()[it1.Index()+1]==l.Model()[it2.Index()]

      invariant (set x | x in old(l.Model())) == (set x | x in l.Model())
      invariant Sorted(l.Model()) && StrictSorted(l.Model()[..it2.Index()])

      invariant l.Iterators() >= old(l.Iterators())

      invariant forall x {:trigger x in l.Repr(), x in old(l.Repr())} | x in l.Repr() && x !in old(l.Repr()) :: fresh(x)
      //forall x | x in l.Repr() - old(l.Repr()) :: fresh(x)
      invariant forall x | x in l.Repr() :: allocated(x)
    {

      if (it1.Peek() == it2.Peek()) {
        ghost var oit2 := it2.Index();
        it2 := l.Erase(it2);
      } else {
        aux := it2.Next();
        aux := it1.Next();
      }
      j := j+1;
    }
  }

}

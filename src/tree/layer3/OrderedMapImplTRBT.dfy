include "../../../src/tree/KeyValue.dfy"
include "../../../src/tree/layer1/UnorderedMap.dfy"
include "../../../src/tree/layer1/OrderedMap.dfy"
include "../../../src/tree/layer1/OrderedSetUtils.dfy"
include "../../../src/tree/layer4/ThreadedLinkedTree.dfy"
include "../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../src/tree/layer4/TRBTree/TRBInsert.dfy"

module OrderedMapImplTRBT {
  import opened KeyValue
  import opened UnorderedMapSpec
  import opened OrderedMapSpec
  import opened OrderedSetUtils
  import opened TRB = TRBTree.Base
  import opened TRBi = TRBTree.TRBInsert
  import opened TRBr = TRBTree.RemoveRoot
  import opened TTNode
  import opened TTree
  import opened ThreadedLinkedTree

  class OrderedMapImplTRBT extends OrderedMap {
    var tree: ThreadedLinkedTree
    var size: nat

    ghost function ReprFamily(n: nat): set<object>
      decreases n
      ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
      reads this, if n == 0 then {} else ReprFamily(n-1)
    {
      if n == 0 then
        {tree}
      else if n == 1 then
        ReprFamily(0) + tree.Repr()
      else
        ReprFamily(n-1)
    }

    ghost predicate Valid()
      reads this, Repr()
    {
      && ReprDepth == 1
      && tree.Valid()
      && tree.Threaded()
      && tree.SearchTree()
      && tree.RedBlackTree()
      && TRB.size(tree.Model()) == size
    }

    ghost function Model(): map<K, V>
      reads this, Repr()
      requires Valid()
    {
      toMapRec(tree.Model())
    }

    constructor()
      ensures Valid()
      ensures fresh(Repr())
    {
      ReprDepth := 1;
      size := 0;
      tree := new ThreadedLinkedTree();
    }

    method Empty() returns (b: bool)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures b == Empty?()

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()))
    {
      assert tree.root == null <==> tree.skeleton.Empty?;
      assert toMap(TreeModelRec(T.Empty)) == map[];
      calc <==> {
        tree.root == null;
        tree.skeleton.Empty?;
        {
          if tree.skeleton.Empty? {
            assert Model() == toMap(TreeModelRec(T.Empty)) == map[];
          }
          if Model() == map[] {
            if tree.skeleton.Thread? {
              assert false;
            }
            if tree.skeleton.Node? {
              assert tree.root.key in Model();
              assert Model() != map[];
              assert false;
            }
          }
        }
        Model() == map[];
      }
      return tree.root == null;
    }

    method Size() returns (s: nat)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures s == |Model()|

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()))
    {
      SizeLemmas(tree.Model());
      return size;
    }

    ghost function Iterators(): set<UnorderedMapIterator>
      reads this, Repr()
      requires Valid()
      ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
      ensures forall it | it in Iterators() :: it is OrderedMapIterator
    {
      {}
    }

    method First() returns (it: UnorderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures it is OrderedMapIterator
      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures it.Traversed() == {}
      ensures (it as OrderedMapIterator).Index() == 0

      ensures Iterators() >= {it} + old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()))

    method Last() returns (it: OrderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures it is OrderedMapIterator
      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this

      ensures it.Index() ==  |Model()|-1

      ensures Iterators() >= {it} + old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()) )

    method Contains(k:K) returns (b:bool)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures b == (k in Model())

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid())::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()) )

    method At(k:K) returns (v:V)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires k in Model()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)
      ensures v == Model()[k]

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid())::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()) )

    method Find(k:K) returns (newt:UnorderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures newt is OrderedMapIterator
      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent()==this
      ensures k in old(Model()) ==> newt.HasPeek?() && key(newt.Peek?()) == k
      ensures k !in old(Model()) ==> newt.Traversed() == Model().Keys && |newt.Traversed()| == |Model().Keys|

      ensures k in old(Model()) ==> (newt as OrderedMapIterator).Index() == |smaller(Model().Keys,k)|
      ensures k !in old(Model()) ==> (newt as OrderedMapIterator).Index() == |Model().Keys|

      ensures Iterators() >= {newt}+old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid())::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()) )

    method Add(k: K,v: V)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())[k:=v]
      ensures if (k in old(Model())) then |Model()| == old(|Model()|)
              else |Model()| == 1 + old(|Model()|)

      ensures Iterators() >= old(Iterators())
    {
      TRBi.TRBInsertRootSpec(tree.Model(), k, v);
      TRBi.IsInsertedSpec(tree.Model(), k);
      TRBi.TRBInsertRootModel(tree.Model(), k, v);
      var isInserted := tree.Insert(k, v);
      if isInserted {
        size := size + 1;
        assert size == TRB.size(tree.Model()) by {
          TRB.SizeLemmas(old(tree.Model()));
          TRB.SizeLemmas(tree.Model());
        }
      } else {
        assert size == TRB.size(tree.Model()) by {
          TRB.SizeLemmas(old(tree.Model()));
          TRB.SizeLemmas(tree.Model());
        }
      }
    }

    method Remove(k: K)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model()) - {k}
      ensures
        if k in old(Model()) then
          |Model()| == old(|Model()|) - 1
        else
          |Model()| == old(|Model()|)

      ensures Iterators() >= old(Iterators())
    {
      TRBr.RemoveRootSpec(tree.Model(), k);
      TRBr.IsRemovedRootSpec(tree.Model(), k);
      TRBr.RemoveRootModel(tree.Model(), k);
      TRB.SizeLemmas(tree.Model());
      var isRemoved := tree.Remove(k);
      TRB.SizeLemmas(tree.Model());
      if isRemoved {
        size := size - 1;
      }
    }

    method Insert(mid: UnorderedMapIterator, k: K, v : V) returns (newt:UnorderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())[k:=v]
      ensures if (k in old(Model())) then |Model()| == old(|Model()|)
              else |Model()| == 1 + old(|Model()|)

      requires mid.Valid()
      requires mid.Parent() == this
      requires mid in Iterators()

      ensures newt is OrderedMapIterator
      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent() == this
      ensures newt.HasPeek?() && newt.Peek?() == (k,v)

      ensures (newt as OrderedMapIterator).Index() == |smaller(Model().Keys,k)|

      ensures Iterators() >= {newt}+old(Iterators())

    method Erase(mid:UnorderedMapIterator) returns (next: UnorderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires mid.Valid()
      requires mid.Parent() == this
      requires mid.HasPeek?()
      requires mid in Iterators()
      ensures Valid()
      ensures Model()== old(Model()) - {key(old(mid.Peek?()))}
      ensures |Model()|==|old(Model())|-1

      ensures next is OrderedMapIterator
      ensures fresh(next)
      ensures next.Valid() && next.Parent() == this
      ensures next.Traversed() == old(mid.Traversed())
      ensures |next.Traversed()| == old(|mid.Traversed()|)

      ensures mid is OrderedMapIterator && (next as OrderedMapIterator).Index() == old((mid as OrderedMapIterator).Index())

      ensures Iterators() >= {next}+old(Iterators())
  }
}
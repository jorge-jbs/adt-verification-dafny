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

  class OrderedMapIteratorTRBT extends OrderedMapIterator {
    const iter: ThreadedLinkedTreeIterator
    ghost const parent: OrderedMapImplTRBT

    ghost function Parent(): UnorderedMap
      reads this
    {
      parent
    }

    ghost predicate PreValid()
      reads this, iter, iter.parent, iter.parent.Repr(), parent, parent.Repr()
    {
      && parent.Valid()
      && iter.parent == parent.tree
      && iter.Valid()
    }

    ghost predicate Valid()
      reads this, Parent(), Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()
    {
      && this in parent.iterators
      && parent.Valid()
      && iter.parent == parent.tree
      && iter.Valid()
    }

    constructor First(parent: OrderedMapImplTRBT)
      requires parent.Valid()
      ensures PreValid()
      ensures this.parent == parent
      ensures fresh(iter)
      //ensures Index() == 0  // TODO
      ensures TRBit.Index(iter.Model(), parent.tree.Model()) == 0  // TODO
    {
      ThreadedRootImp(parent.tree.skeleton);
      this.iter := new ThreadedLinkedTreeIterator.First(parent.tree);
      this.parent := parent;
      new;
      assume {:axiom} TRBit.Index(iter.Model(), parent.tree.Model()) == 0;
    }

    ghost function Index(): int
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures -1 <= Index() <= |parent.Model()|
    {
      TRB.SizeLemmas(parent.tree.Model());
      TRBit.Index(iter.Model(), parent.tree.Model())
    }

    method HasPeek() returns (b:bool)
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)

      ensures Index() == old(Index())

      ensures Traversed() == old(Traversed())
      ensures |Traversed()| == old(|Traversed()|)

      ensures old(HasPeek?()) ==> HasPeek?() && Peek?()==old(Peek?())
      ensures b == HasPeek?()

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()) )
    {
      iter.ValidImp();
      TRBit.HasPeekEq(iter.Model(), parent.tree.Model());
      return iter.HasPeek();
    }

    method Peek() returns (p:(K,V))
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)

      ensures Index() == old(Index())

      ensures Traversed() == old(Traversed()) && Peek?()==old(Peek?())
      ensures |Traversed()| == old(|Traversed()|)

      ensures p == Peek?()
      ensures HasPeek?() && Peek?()==old(Peek?())

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid())::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()) )
    {
      iter.ValidImp();
      TRBit.HasPeekEq(iter.Model(), parent.tree.Model());
      TRBit.PeekEq(iter.Model(), parent.tree.Model());
      iter.PeekEq();
      return iter.Peek();
    }

    method Next()  // 3'
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)

      ensures Traversed() == {key(old(Peek?()))} + old(Traversed())
      ensures |Traversed()| == 1 + old(|Traversed()|)
      ensures Index() == old(Index()) + 1

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && (it != this ==> it.Traversed() == old(it.Traversed())
                                   && |it.Traversed()| == old(|it.Traversed()|)
                                   && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?())))
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) && it != this::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()) )
    {
      assert iter.parent.Valid();
      assert iter.parent.Threaded();
      assert iter.parent.SearchTree();
      assert iter.Valid();
      assert iter.HasPeek() by {
        iter.ValidImp();
        TRBit.HasPeekEq(iter.Model(), parent.tree.Model());
      }
      assert iter.Valid'() by {
        iter.ValidImp();
      }
      assert iter.Peek() == iter.Peek'() by {
        iter.PeekEq();
      }
      assert ThreadedTreeRoot(iter.parent.Model()) by {
        ThreadedRootImp(iter.parent.skeleton);
      }
      ghost var oldIterModel := iter.Model();
      ghost var oldParentModel := iter.parent.Model();
      iter.Next();
      assert
        && fresh(Parent().Repr() - old(Parent().Repr()))
        && allocated(Parent().Repr())
        && Valid()
        && Parent().Valid()
        && Parent() == old(Parent())
        && Parent().Model() == old(Parent().Model())
        && |Parent().Model()| == old(|Parent().Model()|)
        && Parent().Iterators() >= old(Parent().Iterators())
      by {
        //assume false;
      }
      assert
        && Traversed() == {key(old(Peek?()))} + old(Traversed())
        && |Traversed()| == 1 + old(|Traversed()|)
        && Index() == old(Index()) + 1
        && (forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && (it != this ==> it.Traversed() == old(it.Traversed())
                                   && |it.Traversed()| == old(|it.Traversed()|)
                                   && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))))
        && forall it | it in old(Parent().Iterators()) && old(it.Valid()) && it != this::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()) )
      by {
        TRBit.TraversedEq(oldIterModel, oldParentModel);
        TRBit.HasPeekEq(oldIterModel, oldParentModel);
        TRBit.PeekEq(oldIterModel, oldParentModel);
        TRBit.TraversedEq(oldIterModel, oldParentModel);
        iter.ValidImp();
        ThreadedRootImp(iter.parent.skeleton);
        TRBit.TraversedEq(iter.Model(), iter.parent.Model());
        TRBit.NextTraversed(oldIterModel, oldParentModel);

        assert TRBit.Traversed(iter.Model(), iter.parent.Model())
          == TRBit.Traversed(oldIterModel, oldParentModel) + {TRBit.Peek(oldIterModel, oldParentModel).0};

        TRBit.TraversedIndex(oldIterModel, oldParentModel);
        TRBit.TraversedIndex(iter.Model(), iter.parent.Model());
      }
    }

    method {:verify false} Prev()
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      requires HasPeek?()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)

      ensures Index() == old(Index()) - 1

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && (it != this ==> it.Traversed() == old(it.Traversed())
                                   && |it.Traversed()| == old(|it.Traversed()|)
                                   && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?())))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) &&  it != this::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()) )
    {}

    method {:verify false} Copy() returns (it: UnorderedMapIterator)
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures Parent().Model() == old(Parent().Model())
      ensures |Parent().Model()| == old(|Parent().Model()|)

      ensures Index() == old(Index())

      ensures Traversed() == old(Traversed())
      ensures |Traversed()| == old(|Traversed()|)

      ensures old(HasPeek?()) ==> HasPeek?() && Peek?()==old(Peek?())

      ensures fresh(it)
      ensures it.Valid()
      ensures Parent() == it.Parent()
      ensures it is OrderedMapIterator
      ensures  (it as OrderedMapIterator).Index() == Index()
      ensures Traversed() == it.Traversed()
      ensures |Traversed()| == |it.Traversed()|
      ensures HasPeek?() ==> it.HasPeek?() && Peek?()==it.Peek?()

      ensures Parent().Iterators() >= {it} + old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()) )
    {}
  }

  class OrderedMapImplTRBT extends OrderedMap {
    const tree: ThreadedLinkedTree
    var size: nat
    ghost var iterators: set<OrderedMapIteratorTRBT>

    ghost function ReprFamily(n: nat): set<object>
      decreases n
      ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
      reads this, if n == 0 then {} else ReprFamily(n-1)
    {
      if n == 0 then
        {tree} + iterators
      else if n == 1 then
        ReprFamily(0) + tree.Repr() + (set it <- iterators :: it.iter)
      else
        ReprFamily(n-1)
    }

    ghost predicate Valid()
      reads this, Repr()
    {
      && ReprDepth == 1
      && assert tree in ReprFamily(0) && tree.Repr() <= ReprFamily(1); true
      && tree.Valid()
      && tree.Threaded()
      && tree.SearchTree()
      && tree.RedBlackTree()
      && TRB.size(tree.Model()) == size
      && (forall it | it in iterators :: it.parent == this)
      && (
        forall it1, it2 | it1 in iterators && it2 in iterators && it1 != it2 ::
          it1.iter != it2.iter
      )
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
      iterators := {};
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
      iterators
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
    {
      var it' := new OrderedMapIteratorTRBT.First(this);
      assert it'.PreValid();
      assert it'.iter.parent == tree;
      iterators := iterators + {it'};
      assert it'.PreValid() by {
      }
      assert it' in iterators;
      assert it'.Valid();
      assert Valid();
      assert Model() == old(Model());
      assert |Model()| == old(|Model()|);
      it := it';
      assert it is OrderedMapIterator;
      assert fresh(it);
      assert it.Valid();
      assert it.Parent() == this;
      assert (it as OrderedMapIterator).Index() == 0;
      assume {:axiom} it.Traversed() == {};  // esto es falso
      assert Iterators() >= {it} + old(Iterators());
      assert forall it | it in old(Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && it.Traversed() == old(it.Traversed())
        && |it.Traversed()| == old(|it.Traversed()|)
        && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()));
      assert forall it | it in old(Iterators()) && old(it.Valid()) ::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()));
    }

    method {:verify false} Last() returns (it: OrderedMapIterator)
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
    {}

    method {:verify false} Contains(k:K) returns (b:bool)
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
    {}

    method {:verify false} At(k:K) returns (v:V)
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
    {}

    method {:verify false} Find(k:K) returns (newt:UnorderedMapIterator)
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
    {}

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

    method Remove(k: K)  // 2'
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
      assert Valid()
      by {
        assert
          && ReprDepth == 1
          && tree in ReprFamily(0) && tree.Repr() <= ReprFamily(1)
          && tree.Valid()
          && tree.Threaded()
          && tree.SearchTree()
          && tree.RedBlackTree()
          && TRB.size(tree.Model()) == size
        by {
          //assume false;
        }
        assert (forall it | it in iterators :: it.parent == this);
        assert (
          forall it1, it2 | it1 in iterators && it2 in iterators && it1 != it2 ::
            it1.iter != it2.iter
        );
      }
    }

    method {:verify false} Insert(mid: UnorderedMapIterator, k: K, v : V) returns (newt:UnorderedMapIterator)
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
    {}

    method {:verify false} Erase(mid:UnorderedMapIterator) returns (next: UnorderedMapIterator)
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
    {}
  }
}
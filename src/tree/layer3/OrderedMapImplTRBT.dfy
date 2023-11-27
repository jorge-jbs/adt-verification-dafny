include "../../../src/MUtils.dfy"
include "../../../src/tree/KeyValue.dfy"
include "../../../src/tree/layer1/UnorderedMap.dfy"
include "../../../src/tree/layer1/OrderedMap.dfy"
include "../../../src/tree/layer1/OrderedSetUtils.dfy"
include "../../../src/tree/layer4/ThreadedLinkedTree.dfy"
include "../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../src/tree/layer4/TRBTree/TRBInsert.dfy"

module OrderedMapImplTRBT {
  import opened Utils
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
      decreases 0
    {
      parent
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

    constructor (parent: OrderedMapImplTRBT, iter: ThreadedLinkedTreeIterator)
      modifies parent`iterators
      requires parent.Valid()
      requires iter.Valid()
      requires iter.Parent() == parent.tree
      requires forall it <- parent.iterators :: it.iter != iter
      ensures parent.Valid()
      ensures parent.Model() == old(parent.Model())
      ensures |parent.Model()| == |old(parent.Model())|
      ensures parent.Valid()
      ensures Valid()
      ensures this.parent == parent
      ensures HasPeek?() == iter.HasPeek()
      ensures HasPeek?() ==> Peek?() == iter.Peek()
      ensures Index() == iter.Index()
      ensures parent.iterators == {this} + old(parent.iterators)
      ensures forall it <- old(parent.Iterators()) | old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it <- old(parent.Iterators()) | old(it.Valid()) ::
                (it is OrderedMapIterator &&
                 (it as OrderedMapIterator).Index() == old((it as OrderedMapIterator).Index()))
      requires allocated(parent.Repr())
      ensures fresh(parent.Repr() - old(parent.Repr()))
      ensures allocated(parent.Repr())
    {
      this.iter := iter;
      this.parent := parent;
      new;
      parent.iterators := parent.iterators + {this};
      ModelEq();
    }

    lemma HasPeekEq()
      requires Valid()
      ensures HasPeek?() <==> iter.HasPeek()
    {
      calc <==> {
        iter.HasPeek();
        { iter.HasPeekEq(); }
        iter.HasPeek'();
        TRBit.HasPeek(iter.Model());
        {
          KeysAndElems(iter.parent.skeleton);
          TRBit.HasPeekEq(iter.Model(), iter.parent.Model());
        }
        TRBit.HasPeek'(iter.Model(), iter.parent.Model());
        0 <= Index() < |Parent().Model()|;
        HasPeek?();
      }
    }

    lemma PeekEq()
      requires Valid()
      requires HasPeek?()
      requires iter.HasPeek()
      ensures Peek?() == iter.Peek() == iter.Peek'()
    {
      calc == {
        Peek?();
        (
          var k := elemth(Parent().Model().Keys, Index());
          (k, Parent().Model()[k])
        );
        (
          var k := elemth(toMapRec(iter.parent.Model()).Keys, TRBit.Index(iter.Model(), iter.parent.Model()));
          (k, toMapRec(iter.parent.Model())[k])
        );
        TRBit.Peek'(iter.Model(), iter.parent.Model());
        {
          KeysAndElems(iter.parent.skeleton);
          TRBit.PeekEq(iter.Model(), iter.parent.Model());
        }
        TRBit.Peek(iter.Model(), iter.parent.Model());
        iter.Peek'();
        { iter.PeekEq(); }
        iter.Peek();
      }
      assert iter.Peek() == iter.Peek'() by {
        KeysAndElems(iter.parent.skeleton);
        TRBit.PeekEq(iter.Model(), iter.parent.Model());
      }
    }

    lemma PeekEqOfHasPeek()
      requires Valid()
      ensures (HasPeek?() && iter.HasPeek()) ==> Peek?() == iter.Peek() == iter.Peek'()
    {
      HasPeekEq();
      if HasPeek?() {
        PeekEq();
      }
    }

    lemma IndexEq()
      requires Valid()
      ensures Index() == TRBit.Index(iter.Model(), iter.parent.Model())
    {
      TRB.SizeLemmas(parent.tree.Model());
    }

    lemma TraversedEq()
      requires Valid()
      ensures Traversed() == TRBit.Traversed(iter.Model(), iter.parent.Model())
      ensures (HasPeek?() || Index() == |parent.Model()|) ==> |Traversed()| == Index()
    {
      IndexEq();
      iter.ValidImp();
      iter.parent.ThreadedImp();
      TRBit.TraversedEq(iter.Model(), iter.parent.Model());
      HasPeekEq();
      if HasPeek?() || Index() == |parent.Model()| {
        TRBit.TraversedIndex(iter.Model(), iter.parent.Model());
      }
    }

    lemma ModelEq()
      requires Valid()
      ensures TRBit.Valid(iter.Model(), iter.parent.Model())
      ensures ThreadedTreeRoot(iter.parent.Model())
      ensures HasPeek?() <==> iter.HasPeek()
      ensures (HasPeek?() && iter.HasPeek()) ==> Peek?() == iter.Peek() == iter.Peek'()
      ensures Index() == TRBit.Index(iter.Model(), iter.parent.Model())
      ensures Traversed() == TRBit.Traversed(iter.Model(), iter.parent.Model())
      ensures (HasPeek?() || Index() != -1) ==> |Traversed()| == Index()
    {
      iter.ValidImp();
      iter.parent.ThreadedImp();
      HasPeekEq();
      PeekEqOfHasPeek();
      IndexEq();
      TraversedEq();
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

    method Peek() returns (p: (K, V))
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
      ModelEq();
      TRBit.NextTraversed(iter.Model(), iter.parent.Model());
      iter.Next();
      ModelEq();
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
      && (forall it | it in iterators :: it.iter in tree.iterators)
      && (
        forall it1 <- iterators, it2 <- iterators | && it1 != it2 ::
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
      ThreadedRootImp(tree.skeleton);
      TRBit.FirstIndex(tree.Model());
      var iter := tree.First();
      var it' := new OrderedMapIteratorTRBT(this, iter);
      return it' as UnorderedMapIterator;
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

    method {:verify false} Find(k: K) returns (newt:UnorderedMapIterator)
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
      var mid := First();
      var _ := Insert(mid, k, v);
    }

    twostate predicate RemoveIteratorsPrecondition(k: K, oldRepr: set<object>)
      reads this, Repr(), oldRepr
      requires oldRepr == old(Repr())
    {
      && old(Valid())
      && Valid()
      && Model() == old(Model()) - {k}
      && Iterators() >= old(Iterators())
      && (
        forall it
            | it in old(tree.Iterators())
            && old(it.Valid())
            && (old(it.HasPeek()) ==> old(it.Peek().0) != k) ::
          && it.Valid()
          //&& it.Parent() == old(it.Parent())  // obvious since it.parent is const
          && it.Model() == old(it.Model())
          && it.HasPeek() == old(it.HasPeek())
      )
    }

    twostate predicate RemoveIteratorsPostcondition(k: K, oldRepr: set<object>)
      reads this, Repr(), oldRepr
      requires oldRepr == old(Repr())
      requires RemoveIteratorsPrecondition(k, oldRepr)
    {
      forall it | it in old(Iterators())
          && old(it.Valid())
          && (old(it.HasPeek?()) ==> old(it.Peek?().0) != k)
        :: it is OrderedMapIteratorTRBT
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && (it.HasPeek?() <==> old(it.HasPeek?()))
        && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
        && (it.HasPeek?() ==>
          var it' := it as OrderedMapIteratorTRBT;
          if k in old(Model()) && k < it.Peek?().0 then
            && it.Traversed() == old(it.Traversed()) - {k}
            && |it.Traversed()| == old(|it.Traversed()|) - 1
            && it'.Index() == old(it'.Index()) - 1
          else
            && it.Traversed() == old(it.Traversed())
            && |it.Traversed()| == old(|it.Traversed()|)
            && it'.Index() == old(it'.Index())
        )
    }

    twostate lemma RemoveIterators(k: K)
      requires RemoveIteratorsPrecondition(k, old(Repr()))
      ensures RemoveIteratorsPostcondition(k, old(Repr()))
    {
      forall it | it in old(Iterators())
          && old(it.Valid())
          && (old(it.HasPeek?()) ==> old(it.Peek?().0) != k)
        ensures it is OrderedMapIteratorTRBT
        ensures it.Valid()
        ensures it.Parent() == old(it.Parent())
        ensures it.HasPeek?() <==> old(it.HasPeek?())
        ensures it.HasPeek?() ==> it.Peek?() == old(it.Peek?())
        ensures it.HasPeek?() ==>
          var it' := it as OrderedMapIteratorTRBT;
          if k in old(Model()) && k < it.Peek?().0 then
            && it.Traversed() == old(it.Traversed()) - {k}
            && |it.Traversed()| == old(|it.Traversed()|) - 1
            && it'.Index() == old(it'.Index()) - 1
          else
            && it.Traversed() == old(it.Traversed())
            && |it.Traversed()| == old(|it.Traversed()|)
            && it'.Index() == old(it'.Index())

        ensures
          var it' := it as OrderedMapIteratorTRBT;
          (!it.HasPeek?() && old(it'.Index()) == -1) ==>
            && it'.Index() == -1
            && (
              if k in old(Model()) then
                && it'.Traversed() == old(it'.Traversed()) - {k}
                && |it'.Traversed()| == |old(it'.Traversed())| - 1
              else
                && it'.Traversed() == old(it'.Traversed())
                && |it'.Traversed()| == |old(it'.Traversed())|
            )

        ensures
          var it' := it as OrderedMapIteratorTRBT;
          (!it.HasPeek?() && old(it'.Index()) == |old(Model())|) ==>
            && it.Valid()
            && (
              if k in old(Model()) then
                && it'.Index() == old(it'.Index()) - 1
                && it'.Traversed() == old(it'.Traversed()) - {k}
                && |it'.Traversed()| == |old(it'.Traversed())| - 1
              else
                && it'.Index() == old(it'.Index())
                && it'.Traversed() == old(it'.Traversed())
                && |it'.Traversed()| == |old(it'.Traversed())|
            )
      {
        var it' := it as OrderedMapIteratorTRBT;
        assert old(it'.ModelEq(); true);
        it'.ModelEq();
        TRBit.ModelAfterRemove(
          it'.iter.Model(), 
          k, 
          old(it'.iter.parent.Model()), 
          it'.iter.parent.Model()
        );
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
      ensures
        forall it | it in old(Iterators())
            && old(it.Valid())
            && (old(it.HasPeek?()) ==> old(it.Peek?().0) != k)
          :: it is OrderedMapIteratorTRBT
          && it.Valid()
          && it.Parent() == old(it.Parent())
          && (it.HasPeek?() <==> old(it.HasPeek?()))
          && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))
          && (it.HasPeek?() ==>
            var it' := it as OrderedMapIteratorTRBT;
            if k in old(Model()) && k < it.Peek?().0 then
              && it.Traversed() == old(it.Traversed()) - {k}
              && |it.Traversed()| == old(|it.Traversed()|) - 1
              && it'.Index() == old(it'.Index()) - 1
            else
              && it.Traversed() == old(it.Traversed())
              && |it.Traversed()| == old(|it.Traversed()|)
              && it'.Index() == old(it'.Index())
          )
    {
      ghost var oldRepr := Repr();
      TRBr.RemoveRootSpec(tree.Model(), k);
      TRBr.RemoveRootSize(tree.Model(), k);
      TRBr.IsRemovedRootSpec(tree.Model(), k);
      TRBr.RemoveRootModel(tree.Model(), k);
      var isRemoved := tree.Remove(k);
      if isRemoved {
        size := size - 1;
      }
      assert RemoveIteratorsPostcondition(k, oldRepr) by {
        RemoveIterators(k);
      }
    }

    method Insert(mid: UnorderedMapIterator, k: K, v: V) returns (newt:UnorderedMapIterator)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())[k := v]
      ensures if (k in old(Model())) then |Model()| == old(|Model()|)
              else |Model()| == 1 + old(|Model()|)

      requires mid.Valid()
      requires mid.Parent() == this
      requires mid in Iterators()

      ensures newt is OrderedMapIterator
      ensures fresh(newt)
      ensures newt.Valid()
      ensures newt.Parent() == this
      ensures newt.HasPeek?()
      ensures newt.Peek?() == (k, v)

      ensures (newt as OrderedMapIterator).Index() == |smaller(Model().Keys,k)|

      ensures Iterators() >= {newt} + old(Iterators())
    {
      TRBi.TRBInsertRootSpec(tree.Model(), k, v);
      TRBi.TRBInsertRootSize(tree.Model(), k, v);
      TRBi.IsInsertedSpec(tree.Model(), k);
      TRBi.TRBInsertRootModel(tree.Model(), k, v);
      var isInserted, iter := tree.Insert(k, v);
      assert iter.Peek() == (k, v) by {
        calc == {
          iter.Peek();
          { iter.PeekEq(); }
          iter.Peek'();
          TRBit.Peek(TRBit.Find(k), iter.parent.Model());
          { TRBit.FindAfterInsert(k, v, iter.parent.Model()); }
          (k, v);
        }
      }
      if isInserted {
        size := size + 1;
      }
      newt := new OrderedMapIteratorTRBT(this, iter);
    }

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
      ensures Model() == old(Model()) - {key(old(mid.Peek?()))}
      ensures |Model()| == |old(Model())| - 1

      ensures next is OrderedMapIterator
      ensures fresh(next)
      ensures next.Valid()
      ensures next.Parent() == this
      ensures next.Traversed() == old(mid.Traversed())
      ensures |next.Traversed()| == old(|mid.Traversed()|)

      ensures mid is OrderedMapIterator 
      ensures (next as OrderedMapIterator).Index() == old((mid as OrderedMapIterator).Index())

      ensures Iterators() >= {next} + old(Iterators())
    {
      next := mid.Copy();
      next.Next();
      var p := mid.Peek();
      assert next.Valid();
      assert next.Parent() == this;
      assert next in Iterators();
      assert p.0 in Model();
      assert next is OrderedMapIterator;
      assert fresh(next);
      Remove(p.0);
      assert Valid();
      assert Model() == old(Model()) - {p.0};
      assert |Model()| == old(|Model()|) - 1;
      assert fresh(Repr() - old(Repr()));
      assert allocated(Repr()) by {
        assume false;
        Allocated(Repr());
      }
      assert
        && next is OrderedMapIterator
        && fresh(next)
        && next.Valid()
        && next.Parent() == this
        && next.Traversed() == old(mid.Traversed())
        && |next.Traversed()| == old(|mid.Traversed()|)
        && mid is OrderedMapIterator 
        && (next as OrderedMapIterator).Index() == old((mid as OrderedMapIterator).Index())
      by {
        assume false;
      }
      assert Iterators() >= {next} + old(Iterators());
    }
  }
}
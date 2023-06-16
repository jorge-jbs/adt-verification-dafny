include "../../../src/MUtils.dfy"
include "../../../src/tree/layer1/UnorderedMap.dfy"
include "../../../src/tree/layer1/OrderedMapForward.dfy"
include "../../../src/tree/layer1/OrderedSetUtils.dfy"
include "../../../src/tree/layer4/Tree.dfy"
include "../../../src/tree/layer4/TNode.dfy"
include "../../../src/tree/layer4/LinkedTree.dfy"
include "../../../src/tree/layer4/LinkedTree/RBInsert.dfy"
include "../../../src/tree/layer4/LinkedTree/RBRemove.dfy"
include "../../../src/tree/layer1/OrderedMap.dfy"
include "../../../src/tree/layer4/RBTree/Base.dfy"
include "../../../src/tree/layer4/RBTree/RemoveElemth.dfy"

module OrderedMapImpl {
  import opened Utils
  import opened TNode
  import opened KeyValue
  import opened UnorderedMapSpec
  import opened OrderedMapForwardSpec
  import opened OrderedSetUtils
  import opened T = Tree
  import opened LinkedTree
  import opened LinkedTree.SInsert
  import opened LinkedTree.RBInsert
  import opened LinkedTree.RBRemove
  import RB = RBTree.Base
  import RBelemth = RBTree.RemoveElemth

  class OrderedMapIteratorImpl extends OrderedMapForwardIterator {
    var parent: OrderedMapImpl;
    var iter: LinkedTreeIterator;

    constructor {:verify true} First(parent: OrderedMapImpl)
      requires parent.Valid()
      ensures this.parent == parent
      ensures iter.parent == parent.tree
      ensures parent.Valid()
      ensures (set p | p in iter.traversed :: p.0) == {}
      ensures iter.traversed == []
      ensures |iter.traversed| == 0
      ensures iter.Valid()
      ensures fresh(iter)
      ensures parent.Model() != map[] ==>
        && iter.RBStack() != []
        && iter.stackSk[|iter.stackSk|-1].data.key == elemth(parent.Model().Keys, 0)

      ensures forall it | it in old(parent.Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Traversed() == old(it.Traversed())
        && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()))

      requires allocated(parent.Repr())
      ensures allocated(parent.Repr())
    {
      this.parent := parent;
      this.iter := new LinkedTreeIterator.First(parent.tree);
      new;
      assert FirstPost: iter.parent.MapModel() != map[] ==> iter.HasPeek() && key(iter.Peek()) == elemth(iter.parent.MapModel().Keys, 0);
      assume forall it | it in old(parent.Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Traversed() == old(it.Traversed())
        && (it.HasPeek?() ==> it.Peek?() == old(it.Peek?()));
      if parent.Model() != map[] {
        assert iter.parent.MapModel() != map[];
        assert iter.RBStack() != [];
        assert key(iter.Peek()) == elemth(iter.parent.MapModel().Keys, 0) by {
          reveal FirstPost;
        }
        assert iter.stackSk[|iter.stackSk|-1].data.key == elemth(parent.Model().Keys, 0);
      }
    }

    function Parent(): UnorderedMap
      reads this
      ensures Parent() is OrderedMapImpl
    {
      parent
    }

    lemma ParentIterators()
      requires Parent().Valid() ==> parent.iters == Parent().Iterators()
    {
      if Parent().Valid() {
        assert Parent() == parent;
        calc == {
          Parent().Iterators();
          parent.Iterators();
          parent.iters;
        }
      }
    }

    predicate Valid()
      reads this, Parent(), Parent().Repr()
      ensures Valid() ==> Parent().Valid() && this in Parent().Iterators()
    {
      ParentIterators();
      && this in parent.iters
      && iter.parent == parent.tree
      && parent.Valid()

      && (forall sk: tree<TNode> | sk in iter.stackSk :: elems(sk) <= elems(parent.tree.skeleton))
      && iter.Valid()
    }

    function Index(): int
      reads this, Parent(), Parent().Repr()
      requires Valid()
      requires Parent().Valid()
      ensures 0 <= Index() <= |Parent().Model()|
    {
      iter.TraversedSizeLeMapModelSize();
      |iter.traversed|
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

      ensures old(HasPeek?()) ==> HasPeek?() && Peek?() == old(Peek?())
      ensures b == HasPeek?()

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()) )
    {
      b := iter.stack != [];
      assert b == HasPeek?() by {
        iter.HasPeekConditionCard();
      }
    }
    
    lemma TraversedTraversed()
      requires Valid()
      requires Parent().Valid()
      ensures Traversed() == RB.orderKeysToSet(iter.traversed)
    {
      if |iter.traversed| == |parent.Model()| {
        calc == {
          Traversed();
          { assert Index() == |iter.traversed|; }
          parent.Model().Keys;
          { RB.OrderKeysIsMapKeys(iter.parent.TreeModel()); }
          RB.orderKeysToSet(RB.inorder(iter.parent.TreeModel()));
          { RB.SizeLemmas(iter.parent.TreeModel()); }
          RB.orderKeysToSet(iter.traversed);
        }
      } else {
        RB.OrderKeysIsMapKeys(iter.parent.TreeModel());
        RB.SizeLemmas(iter.parent.TreeModel());
        iter.HasPeekConditionCard();
        iter.TraversedSmaller();
      }
    }

    method {:verify false} Next()
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

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && (it != this ==> it.Traversed() == old(it.Traversed())
                                   && |it.Traversed()| == old(|it.Traversed()|)
                                   && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?())))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) && it != this:://NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()) )
    {
      assert iter.RBStack() != [] by {
        assert 0 <= Index() == |iter.traversed| < |Parent().Model()|;
        iter.HasPeekConditionCard();
        assert |iter.traversed| < |iter.parent.MapModel()|;
        assert iter.stackSk != [];
      }
      assert key(Peek?()) == iter.stack[|iter.stack|-1].key by {
        iter.PeekElemth();
        calc == {
          iter.stack[|iter.stack|-1].key;
          iter.stackSk[|iter.stackSk|-1].data.key;
          elemth(iter.parent.MapModel().Keys, |iter.traversed|);
          elemth(Parent().Model().Keys, Index());
          key(Peek?());
        }
      }
      assert OldTraversedTraversed: Traversed() == RB.orderKeysToSet(iter.traversed) by {
        TraversedTraversed();
      }
      var k, v := iter.Next();
      assert fresh(Parent().Repr() - old(Parent().Repr()));
      assert allocated(Parent().Repr());
      assert Valid();
      assert Parent().Valid();
      assert Parent() == old(Parent());
      assert Parent().Model() == old(Parent().Model());
      assert |Parent().Model()| == old(|Parent().Model()|);

      assert k == key(old(Peek?()));
      assert Traversed() == RB.orderKeysToSet(iter.traversed) by {
        TraversedTraversed();
      }
      assert old(Traversed()) == old(RB.orderKeysToSet(iter.traversed)) by {
        reveal OldTraversedTraversed;
      }
      assert Traversed() == {key(old(Peek?()))} + old(Traversed());
      assert |Traversed()| == 1 + old(|Traversed()|);

      assert Parent().Iterators() >= old(Parent().Iterators());
      assume forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && (it != this ==> it.Traversed() == old(it.Traversed())
                                   && |it.Traversed()| == old(|it.Traversed()|)
                                   && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?())));

      assume forall it | it in old(Parent().Iterators()) && old(it.Valid()) && it != this::
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()));
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
      ensures HasPeek?() && Peek?() == old(Peek?())

      ensures Parent().Iterators() >= old(Parent().Iterators())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()):://NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()))
    {
      iter.HasPeekConditionCard();
      var n := iter.stack[|iter.stack|-1];
      p := (n.key, n.value);

      assert p == Peek?() by {
        iter.PeekElemth();
      }
    }

    method Copy() returns (it: UnorderedMapIterator)
      modifies this, Parent(), Parent().Repr()
      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())

      requires Valid()
      requires Parent().Valid()
      ensures fresh(it)
      ensures Valid()
      ensures Parent().Valid()
      ensures Parent() == old(Parent())
      ensures Parent().Model() == old(Parent().Model())
      ensures Traversed() == old(Traversed())
      ensures HasPeek?() ==> Peek?()==old(Peek?())

      ensures it.Valid()
      ensures Parent().Iterators() >= {it} + old(Parent().Iterators())
      ensures Parent() == it.Parent()
      ensures Traversed() == it.Traversed() && (it.HasPeek?() ==> Peek?()==it.Peek?())
      ensures forall it | it in old(Parent().Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && it.Traversed() == old(it.Traversed())
        && (it.HasPeek?() ==> it.Peek?()==old(it.Peek?()))
  }

  class OrderedMapImpl extends OrderedMapForward {
    var tree: LinkedTree;
    ghost var iters: set<OrderedMapIteratorImpl>;
    var size: nat;

    function Repr0(): set<object>
      reads this
    {
      {tree} + iters
    }

    function Repr1(): set<object>
      reads this, Repr0()
    {
      Repr0() + tree.Repr() + (set it | it in iters :: it.iter)
    }

    function ReprFamily(n: nat): set<object>
      decreases n
      ensures n > 0 ==> ReprFamily(n) >= ReprFamily(n-1)
      reads this, if n == 0 then {} else ReprFamily(n-1)
    {
      if n == 0 then Repr0()
      else Repr1()
    }

    predicate Valid()
      reads this, Repr()
    {
      && ReprDepth == 1
      && assert ReprFamily(0) <= ReprFamily(1); true
      && tree.Valid()
      && tree.SearchTree()
      && tree.RedBlackTree()
      && size == |tree.MapModel()|
      && (forall it | it in iters :: it.parent == this && {it} !! {this})
    }

    function Model(): map<K, V>
      reads this, Repr()
      requires Valid()
    {
      tree.MapModel()
    }

    constructor()
      ensures Valid()
      ensures Model() == map[]
      ensures fresh(Repr())
      ensures allocated(Repr())
    {
      tree := new LinkedTree();
      size := 0;
      iters := {};
      ReprDepth := 1;
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

      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()))
    {
      b := tree.root == null;
      if !b {
        assert !tree.TreeModel().Empty?;
        assert tree.MapModel().Keys == RB.keys(tree.TreeModel());
      }
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

      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()))
    {
      RB.SizeKeys(tree.TreeModel());
      calc == {
        RB.size(tree.TreeModel());
        |RB.keys(tree.TreeModel())|;
        { assert RB.keys(tree.TreeModel()) == tree.MapModel().Keys; }
        |tree.MapModel().Keys|;
        |tree.MapModel()|;
      }
      return size;
    }

   function Iterators(): set<UnorderedMapIterator>
      reads this, Repr()
      requires Valid()
      ensures forall it | it in Iterators() :: it in Repr() && it.Parent() == this
      ensures forall it | it in Iterators() :: it is OrderedMapForwardIterator
    {
      iters
    }

    lemma AddSetComm<A>(a: set<A>, b: set<A>)
      ensures a + b == b + a
    {}

    method {:verify true} First() returns (it: UnorderedMapIterator)  // 1'
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

      ensures it is OrderedMapForwardIterator
      ensures fresh(it)
      ensures it.Valid()
      ensures it.Parent() == this
      ensures it.Traversed() == {}

      ensures (it as OrderedMapForwardIterator).Index() == 0

      ensures Iterators() >= {it} + old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()))
    {
      var iter := new OrderedMapIteratorImpl.First(this);
      iters := iters + {iter};
      it := iter;
      calc == {
        Repr();
        Repr1();
        Repr0() + tree.Repr() + (set it | it in iters :: it.iter);
        { AddSetComm({tree}, iters); assert Repr0() == {tree} + iters == iters + {tree}; }
        iters + {tree} + tree.Repr() + (set it | it in iters :: it.iter);
        {
          assert iters == old(iters) + {iter};
          assert {tree} == old({tree});
          assert tree.Repr() == old(tree.Repr());
          assert (set it | it in iters :: it.iter) == (set it | it in old(iters) :: it.iter) + {iter.iter};
        }
        old(iters) + {iter} + old({tree}) + old(tree.Repr()) + (set it | it in old(iters) :: it.iter) + {iter.iter};
        old(Repr()) + {iter} + {iter.iter};
      }
      assert Repr() - old(Repr()) == {iter} + {iter.iter};
      assert fresh(Repr() - old(Repr()));
      assert allocated(Repr());
      assert Valid();
      assert Model() == old(Model());
      assert |Model()| == old(|Model()|);
      assert it is OrderedMapForwardIterator;
      assert fresh(it);
      assert it.Valid() by {
        assert iter in iter.parent.iters;
        assert iter.iter.parent == iter.parent.tree;
        assert iter.parent.Valid();
        assert (forall sk: tree<TNode> | sk in iter.iter.stackSk :: elems(sk) <= elems(iter.parent.tree.skeleton));
        assert iter.iter.Valid();
        assert iter.Valid();
      }
      assert it.Parent() == this;
      assert iter.Index() == 0 by {
        iter.iter.HasPeekConditionCard();
      }
      assert it.Traversed() == {};

      assume Iterators() >= {it} + old(Iterators());
      assume forall it | it in old(Iterators()) && old(it.Valid()) ::
                && it.Valid()
                && it.Parent() == old(it.Parent())
                && it.Traversed() == old(it.Traversed())
                && |it.Traversed()| == old(|it.Traversed()|)
                && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()));

      assume forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
                (it is OrderedMapForwardIterator &&
                 (it as OrderedMapForwardIterator).Index() == old((it as OrderedMapForwardIterator).Index()));
    }

    method {:verify false} Contains(k: K) returns (b: bool)
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

  /*
      ensures forall it | it in old(Iterators()) && old(it.Valid()):://NEW
        (it is OrderedSetIterator &&
        (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index()) )    {
        assert tree.tree.Repr() <= Repr();
        b := tree.Search(k);
      }
        */
    {
      var foundNode := tree.Find(k);
      return foundNode != null;
    }

    method {:verify false} Find(x: K) returns (newt: UnorderedMapIterator)
     modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())
      ensures |Model()| == old(|Model()|)

  /*
      ensures newt is OrderedSetIterator
      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent()==this
      ensures x in old(Model()) ==> newt.HasPeek?() && newt.Peek?() == x
      ensures x !in old(Model()) ==> newt.Traversed() == Model() && |newt.Traversed()| == |Model()|

      ensures x in old(Model()) ==> (newt as OrderedSetIterator).Index() == |smaller(Model(),x)| //NEW
      ensures x !in old(Model()) ==> (newt as OrderedSetIterator).Index() == |Model()|

      ensures Iterators() >= {newt}+old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && it.Traversed() == old(it.Traversed())
        && |it.Traversed()| == old(|it.Traversed()|)
        && (old(it.HasPeek?()) ==> it.HasPeek?() && it.Peek?()==old(it.Peek?()))

      ensures forall it | it in old(Iterators()) && old(it.Valid()) :://NEW
        (it is OrderedSetIterator &&
        (it as OrderedSetIterator).Index() == old((it as OrderedSetIterator).Index()))
    {
      var foundNode := Find();
    }
      */

    method {:verify false} At(k: K) returns (v: V)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      requires k in Model()
      ensures Valid()
      ensures Model() == old(Model())
      ensures v == Model()[k]

      ensures Iterators() >= old(Iterators())
      ensures forall it | it in old(Iterators()) && old(it.Valid()) ::
        && it.Valid()
        && it.Parent() == old(it.Parent())
        && it.Traversed() == old(it.Traversed())
        && (it.HasPeek?() ==> it.Peek?()==old(it.Peek?()))
    {
      var foundNode := tree.Find(k);
      return foundNode.value;
    }

    method {:verify false} Add(k: K, v: V)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      ensures Model() == old(Model())[k := v]
      ensures if (k in old(Model())) then |Model()| == old(|Model()|) else |Model()| == 1 + old(|Model()|)
      ensures Iterators() >= old(Iterators())
    {
      var b := Contains(k);
      tree.RBInsert(k, v);
      if !b {
        size := size + 1;
      }
    }

    lemma MapDiffSize(m: map<K, V>, k: K)
      ensures k in m && m != map[] ==> |m - {k}| == |m| - 1
      ensures k !in m ==> |m - {k}| == |m|
    {
      assert forall p: map<K, V> :: |p| == |p.Keys|;
    }

    method {:verify false} Remove(k:K)
      modifies this, Repr()
      requires allocated(Repr())
      ensures fresh(Repr() - old(Repr()))
      ensures allocated(Repr())

      requires Valid()
      ensures Valid()
      //ensures Model() == map k' | k' in old(Model()) && k' != k :: old(Model())[k']
      ensures Model() == old(Model()) - {k}
      ensures Iterators() >= old(Iterators())
    {
      MapDiffSize(tree.MapModel(), k);
      var b := Contains(k);
      tree.RBRemove(k);
      assert tree.MapModel() == old(tree.MapModel()) - {k};
      if b {
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
      ensures if (k in old(Model())) then |Model()| == old(|Model()|) else |Model()| == 1 + old(|Model()|)

      requires mid.Valid()
      requires mid.Parent() == this
      requires mid in Iterators()

      ensures newt is OrderedMapForwardIterator
      ensures fresh(newt)
      ensures newt.Valid() && newt.Parent() == this
      ensures newt.HasPeek?() && newt.Peek?() == (k,v)

      ensures (newt as OrderedMapForwardIterator).Index() ==  |smaller(Model().Keys,k)|//NEW

      ensures Iterators() >= {newt}+old(Iterators())
    //points either to the inserted elemento or to the already existing one

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
      ensures Model()== old(Model())- {key(old(mid.Peek?()))} //map k | k in old(Model()) && k != key(old(mid.Peek?()))::old(Model())[k]
      ensures |Model()|==|old(Model())|-1

      ensures next is OrderedMapForwardIterator
      ensures fresh(next)
      ensures next.Valid() && next.Parent() == this
      ensures next.Traversed() == old(mid.Traversed())
      ensures |next.Traversed()| == old(|mid.Traversed()|)

      ensures mid is OrderedMapForwardIterator && (next as OrderedMapForwardIterator).Index() == old((mid as OrderedMapForwardIterator).Index())

      ensures Iterators() >= {next}+old(Iterators())
  }
}
include "../../../src/MUtils.dfy"
include "../../../src/tree/layer1/OrderedSetUtils.dfy"
include "../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../src/tree/layer4/TRBTree/Iterator.dfy"
include "../../../src/tree/layer4/TRBTree/TRBInsert.dfy"
include "../../../src/tree/layer4/TTree.dfy"
include "../../../src/tree/KeyValue.dfy"
include "../../../src/tree/layer4/TTNode.dfy"
include "../../../src/tree/layer4/ThreadedLinkedTree/TRBInsert.dfy"
include "../../../src/tree/layer4/ThreadedLinkedTree/RemoveRoot.dfy"
include "../../../src/tree/layer4/ThreadedLinkedTree/Min.dfy"
include "../../../src/MUtils.dfy"

module ThreadedLinkedTree {
  import opened Utils
  import opened TTNode
  import TRB = TRBTree.Base
  import TRBi = TRBTree.TRBInsert
  import TRBr = TRBTree.RemoveRoot
  import TRBit = TRBTree.Iterator
  import opened T = TTree
  import opened KeyValue
  import opened TRBInsert
  import opened R = RemoveRoot
  import opened Min
  import opened OrderedSetUtils

  class ThreadedLinkedTreeIterator {
    var node: TTNode?
    ghost var isPastTheEnd: bool
    ghost var parent: ThreadedLinkedTree

    ghost predicate Valid()
      reads this, parent
    {
      node != null ==> node in elems(parent.skeleton)
    }

    ghost function Skeleton(): ttree<TTNode>
      reads this, parent, parent.Repr()
      requires Valid()
      requires parent.Valid()
      requires parent.SearchTree()
    {
      if node == null then
        Empty
      else
        GetSk(node, parent.root, parent.skeleton)
    }

    ghost function Model(): TRBit.iter
      reads this, node, parent, parent.Repr()
      requires Valid()
      requires parent.Valid()
      requires parent.SearchTree()
    {
      if node == null then
        if isPastTheEnd then
          TRBit.PastTheEnd
        else
          TRBit.PastTheBeginning
      else
        TRBit.Link(TreeModelRec(Skeleton()))
    }

    ghost predicate Valid'()
      reads this, node, parent, parent.Repr()
      requires Valid()
      requires parent.Valid()
      requires parent.SearchTree()
    {
      TRBit.Valid(Model(), parent.Model())
    }

    lemma ValidImp()
      requires parent.Valid()
      requires parent.SearchTree()
      ensures Valid() ==> Valid'()
    {
      // Esto es cierto pero no sé por qué Dafny lo demuestra tan fácil... sospechoso...
      // (podría quitar todos los asertos de abajo)
      // Edit: esto es porque GetSk es equivalente a GetSubtree, que dice que es un subárbol de la raíz
      if Valid() {
        assert node != null ==> TRB.Subtree(Model().link, parent.Model());
        if node != null {
          assert || parent.Model() == Model().link
          || (
            && parent.Model().Node?
            && (TRB.Subtree(Model().link, parent.Model().left) || TRB.Subtree(Model().link, parent.Model().right))
          );
        }
        assert TRBit.Valid(Model(), parent.Model());
      }
    }

    constructor Root(parent: ThreadedLinkedTree)
    {
      this.node := parent.root;
      this.isPastTheEnd := false;
      this.parent := parent;
    }

    ghost function Index(): int
      reads this, node, parent, parent.Repr()
      requires Valid()
      requires parent.Valid()
      requires parent.SearchTree()
    {
      TRBit.Index(Model(), parent.Model())
    }

    ghost predicate HasPeek()
      reads this
    {
      node != null
    }

    ghost predicate HasPeek'()
      reads this, node, parent, parent.Repr()
      requires Valid()
      requires parent.Valid()
      requires parent.SearchTree()
    {
      TRBit.HasPeek(Model())
    }

    lemma HasPeekEq()
      requires Valid()
      requires parent.Valid()
      requires parent.SearchTree()
      ensures HasPeek() <==> HasPeek'()
    {}

    ghost function Peek(): (K, V)
      reads this, node, parent, parent.Repr()
      requires Valid()
      requires parent.Valid()
      requires parent.SearchTree()
      requires HasPeek()
    {
      TRBit.Peek(Model(), parent.Model())
    }

    method Next()  // 20"
      modifies this
      requires Valid()
      requires HasPeek()
      requires parent.Valid()
      requires parent.Threaded()
      requires parent.SearchTree()
      requires TRB.ThreadedTreeRoot(parent.Model())

      ensures Valid()
      ensures parent.Valid()
      ensures parent.Threaded()
      ensures parent.SearchTree()
      ensures Model() == TRBit.Next(old(Model()), old(parent.Model()))

      requires allocated(parent.Repr())
      ensures allocated(parent.Repr())
    {
      if node.right == null {
        assert ValidRec(node.right, Skeleton().right);
        assert Skeleton().right.Empty?;
        assert TreeModelRec(Skeleton()).right.Empty?;
        assert Model().link.right.Empty?;
        node := null;
        isPastTheEnd := true;
      } else if node.isThreadRight {
        assert ValidChild(node.right, Skeleton().right, true);
        assert Skeleton().right.Thread?;
        assert TreeModelRec(Skeleton()).right.Thread?;
        assert Model().link.right.Thread?;
        assert node.right in elems(parent.skeleton) by {
          assert node.right in elemsAndThreads(Skeleton());
          calc {
            elemsAndThreads(Skeleton());
            <= {parent.SubtreeOfInElems(node, Skeleton());} elemsAndThreads(parent.skeleton);
            == {parent.ElemsOfThread();} elems(parent.skeleton);
          }
        }
        node := node.right;
        assert Model() == TRBit.Next(old(Model()), old(parent.Model())) by {
          calc == {
            TRBit.Next(old(Model()), old(parent.Model()));
            TRBit.Link(TRB.GetSubtree(old(parent.Model()), old(TreeModelRec(Skeleton()).right.thread)));
            TRBit.Link(TRB.GetSubtree(old(parent.Model()), old(node.right.key)));
            Model();
          }
        }
      } else {
        assert ValidRec(node.right, Skeleton().right);
        assert Skeleton().right.Node?;
        assert TreeModelRec(Skeleton()).right.Node?;
        assert Model().link.right.Node?;
        assert node.right in elems(Skeleton());
        assert elems(Skeleton()) <= elems(parent.skeleton) by {
          calc {
            elems(Skeleton());
            <= {ElemsInElemsAndThreads(Skeleton());} elemsAndThreads(Skeleton());
            <= {parent.SubtreeOfInElems(node, Skeleton());} elemsAndThreads(parent.skeleton);
            == {parent.ElemsOfThread();} elems(parent.skeleton);
          }
        }
        parent.ElemsOfThread();
        ghost var sk;
        node, sk := Min.Min(node.right, Skeleton().right);
        assert sk == GetSk(node, parent.root, parent.skeleton) by {
          EqOfValid(node, sk, GetSk(node, parent.root, parent.skeleton));
        }
      }
    }
  }

  class ThreadedLinkedTree {
    var root: TTNode?
    ghost var skeleton: ttree<TTNode>

    ghost function Repr(): set<object>
      reads this
    {
      elems(skeleton)
    }

    ghost predicate Valid()
      reads this, Repr()
    {
      ValidRec(root, skeleton)
    }

    constructor()
      ensures Valid()
      ensures Threaded()
      ensures Model().Empty?
      ensures SearchTree()
      ensures RedBlackTree()
      ensures fresh(Repr())
      ensures allocated(Repr())
    {
      root := null;
      skeleton := Empty;
    }

    ghost predicate SearchTree()
      reads this, Repr()
      requires Valid()
    {
      SearchTreeRec(skeleton)
    }

    ghost predicate Threaded()
      reads this, Repr()
      requires Valid()
    {
      ThreadedRoot(skeleton)
    }

    ghost function Model(): TRB.trbtree
      reads this, elems(skeleton)
    {
      TreeModelRec(skeleton)
    }

/*
    ghost function MapModel(): map<K, V>
      reads this, elems(skeleton)
      requires Valid()
      requires SearchTree()
    {
      RB.toMap(TreeModel())
    }
    */

    /*
    method Find(k: K) returns (foundNode: TTNode?)
      requires Valid()
      requires SearchTree()

      ensures foundNode != null <==> k in RB.keys(TreeModel())
      ensures foundNode != null ==> foundNode.key == k
      ensures foundNode != null ==> foundNode.value == RB.Get(TreeModel(), k)

      requires allocated(Repr())
      ensures allocated(Repr())
    {
      foundNode := FindRec(root, skeleton, k);
    }
    */

    /*
    method {:verify false} Insert(k: K, v: V)
      modifies this, Repr()
      requires Valid()
      requires SearchTree()
      ensures Valid()
      ensures SearchTree()
      ensures MapModel() == old(MapModel())[k := v]

      requires allocated(Repr())
      ensures fresh(Repr()-old(Repr()))
      ensures allocated(Repr())
    {
      ghost var z;
      root, skeleton, z := SInsertRec(root, skeleton, k, v);
      RBs.SInsertSpec(old(TreeModelRec(skeleton)), k, v);
      RBs.SInsertModel(old(TreeModelRec(skeleton)), k, v);
    }
    */

    lemma ElemsOfThread()
      requires Valid()
      requires Threaded()
      ensures elems(skeleton) == elemsAndThreads(skeleton)
    {
      T.ElemsAndThreads(skeleton);
    }

    lemma SubtreeOfInElems(node: TTNode?, sk: ttree<TTNode>)
      requires ValidRec(node, sk)
      requires Valid()
      requires node in elems(skeleton)
      ensures T.Subtree(sk, skeleton)
      ensures elemsAndThreads(sk) <= elemsAndThreads(skeleton)
    {
      SubtreeOfInElemsRoot(node, sk, root, skeleton);
    }

    ghost predicate RedBlackTree()
      reads this, elems(skeleton)
    {
      TRB.RedBlackTreeRoot(TreeModelRec(skeleton))
    }

    method Insert(k: K, v: V) returns (isInserted: bool)
      modifies this, Repr()

      requires Valid()
      requires Threaded()
      requires SearchTree()
      requires RedBlackTree()

      ensures Valid()
      ensures Threaded()
      ensures SearchTree()
      ensures RedBlackTree()
      ensures Model() == TRBi.TRBInsertRoot(old(Model()), k, v)
      ensures isInserted <==> TRBi.IsInserted(old(Model()), k)

      requires allocated(Repr())
      ensures fresh(Repr()-old(Repr()))
      ensures allocated(Repr())
    {
      TRBi.TRBInsertRootSpec(TreeModelRec(skeleton), k, v);
      var insertedNode;
      root, skeleton, insertedNode, isInserted := TRBInsertRoot(root, skeleton, k, v);
    }

    method Remove(k: K) returns (isRemoved: bool)
      modifies this, Repr()

      requires Valid()
      requires Threaded()
      requires SearchTree()
      requires RedBlackTree()

      ensures Valid()
      ensures Threaded()
      ensures SearchTree()
      ensures RedBlackTree()
      ensures TRBr.RemoveRoot(old(Model()), k).Some?
      ensures Model() == TRBr.RemoveRoot(old(Model()), k).unwrap
      ensures isRemoved <==> TRBr.IsRemovedRoot(old(Model()), k)

      requires allocated(Repr())
      ensures fresh(Repr()-old(Repr()))
      ensures allocated(Repr())
    {
      TRBr.RemoveRootSpec(TreeModelRec(skeleton), k);
      root, skeleton, isRemoved := R.RemoveRoot(root, skeleton, k);
    }
  }

  method {:verify false} TestThreadedLinkedTree()
  {
    var t := new ThreadedLinkedTree();
    assert TRB.toMap(t.Model()) == map[];

    TRBi.TRBInsertRootModel(t.Model(), 1, 0);
    var _ := t.Insert(1, 0);
    assert TRB.toMap(t.Model()) == map[1 := 0];

    TRBi.TRBInsertRootModel(t.Model(), 3, 2);
    var _ := t.Insert(3, 2);
    assert TRB.toMap(t.Model()) == map[1 := 0, 3 := 2];

    TRBi.TRBInsertRootModel(t.Model(), 2, 1);
    var _ := t.Insert(2, 1);
    assert TRB.toMap(t.Model()) == map[1 := 0, 3 := 2, 2 := 1];
  }
}
include "../../../src/MUtils.dfy"
include "../../../src/tree/layer1/OrderedSetUtils.dfy"
include "../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../src/tree/layer4/TRBTree/Iterator.dfy"
include "../../../src/tree/layer4/TRBTree/TRBInsert.dfy"
include "../../../src/tree/layer4/TTree1.dfy"
include "../../../src/tree/KeyValue.dfy"
include "../../../src/tree/layer4/TTNode1.dfy"
include "../../../src/tree/layer4/ThreadedLinkedTree1/TRBInsert.dfy"
include "../../../src/MUtils.dfy"

module ThreadedLinkedTree {
  import opened Utils
  import opened TTNode
  import TRB = TRBTree.Base
  import TRBi = TRBTree.TRBInsert
  import TRBit = TRBTree.Iterator
  import opened T = Tree
  import opened KeyValue
  import opened TRBInsert
  import opened OrderedSetUtils

  class ThreadedLinkedTreeIterator {
    var node: TTNode?
    ghost var sk: ttree<TTNode>
    ghost var isPastTheEnd: bool
    ghost var parent: ThreadedLinkedTree

    function ItModel(): TRBit.iter
      reads this, node, elems(sk)
      requires ValidRec(node, sk)
    {
      if node == null then
        if isPastTheEnd then
          TRBit.PastTheEnd
        else
          TRBit.PastTheBeginning
      else
        TRBit.Link(TreeModelRec(sk))
    }

    predicate Valid()
      reads this, elems(sk), parent, parent.Repr()
    {
      && (node != null ==> elems(sk) <= elems(parent.skeleton))
      && ValidRec(node, sk)
      && TRBit.Valid(ItModel(), parent.TreeModel())
    }

    constructor Root(parent: ThreadedLinkedTree)
    {
      this.node := parent.root;
      this.sk := parent.skeleton;
      this.isPastTheEnd := false;
      this.parent := parent;
    }

/*
    function Index(): int
      reads this, parent, parent.Repr()
      /*
      requires Valid()
      requires parent.Valid()
      ensures 0 <= Index() <= |parent.MapModel()|
      */
    {
      if node == null then
        if isPastTheEnd then
          TRB.size(parent.TreeModel())
        else
          0
      else
        TRB.sizeSmaller(parent.TreeModel(), node.key)
    }

    function Traversed(): set<K>
      reads this, parent, parent.Repr()
    {
      if node == null then
        if isPastTheEnd then
          TRB.orderKeysToSet(TRB.inorder(parent.TreeModel()))
        else
          {}
      else
        TRB.orderKeysToSet(TRB.smallerInorder(parent.TreeModel(), node.key))
    }
*/
    function Index(): int
      reads this, node, elems(sk), parent, elems(parent.skeleton)
      requires ValidRec(node, sk)
    {
      TRBit.Index(ItModel(), parent.TreeModel())
    }

    predicate HasPeek()
      reads this, node, elems(sk)
      requires ValidRec(node, sk)
    {
      TRBit.HasPeek(ItModel())
    }

    function Peek(): (K, V)
      reads this, node, elems(sk), parent, elems(parent.skeleton)
      requires ValidRec(node, sk)
      requires HasPeek()
    {
      TRBit.Peek(ItModel(), parent.TreeModel())
    }

    static function SkGet'(node: TTNode, root: TTNode?, rootSk: ttree<TTNode>): ttree<TTNode>
      reads elems(rootSk)
      requires ValidRec(root, rootSk)
      requires node in elems(rootSk)
      requires TRB.SearchTree(TreeModelRec(rootSk))
      ensures ValidRec(node, SkGet'(node, root, rootSk))
      ensures node.key in TRB.keys(TreeModelRec(rootSk))
      ensures TreeModelRec(SkGet'(node, root, rootSk)) == TRB.GetSubtree(TreeModelRec(rootSk), node.key)

    static function SkGet(sk: ttree<TTNode>, k: K): ttree<TTNode>
      reads elems(sk)
      requires TRB.SearchTree(TreeModelRec(sk))
      requires k in TRB.keys(TreeModelRec(sk))
      ensures TreeModelRec(SkGet(sk, k)) == TRB.GetSubtree(TreeModelRec(sk), k)

    method Next()
      modifies this
      requires Valid()
      requires HasPeek()
      requires parent.Valid()
      requires parent.SearchTree()
      ensures Valid()
      ensures ItModel() == TRBit.Next(old(ItModel()), old(parent.TreeModel()))
    {
      assert node != null;
      if node.isThreadRight {
        assert ValidRecP(node.right, sk.right, node.isThreadRight);
        assert TreeModelRecP(sk.right).Thread?;
        assert node.right != null;
        assert node.right in elems(parent.skeleton) by {
          assert node in elems(parent.skeleton);
          assert elems(sk) <= elems(parent.skeleton);
          assert elems(sk.right.child) <= elemsP(sk.right) <= elems(sk);
          assert node.right in elems(sk);
        }
        assume false;
        node := node.right;
        /*
        assert node.key in TRB.keys(TreeModelRec(sk)) by {
          assume false;
        }
        sk := SkGet(parent.skeleton, node.key);
        */
        assert node in elems(parent.skeleton);
        sk := SkGet'(node, parent.root, parent.skeleton);
        assume false;
      } else if node.right == null {
        assert ValidRecP(node.right, sk.right, node.isThreadRight);
        assert TreeModelRecP(sk.right) == TRB.Child(TRB.Empty());
        node := null;
        sk := Empty;
        isPastTheEnd := true;
      } else {
        assume false;
      }
    }
  }

  class ThreadedLinkedTree {
    var root: TTNode?;
    ghost var skeleton: ttree<TTNode>;

    function Repr(): set<object>
      reads this
    {
      elems(skeleton)
    }

    predicate Valid()
      reads this, Repr()
    {
      ValidRec(root, skeleton)
    }

    constructor()
      ensures Valid()
      ensures TreeModel().Empty?
      ensures SearchTree()
      ensures RedBlackTree()
      ensures fresh(Repr())
      ensures allocated(Repr())
    {
      root := null;
      skeleton := Empty;
    }

    predicate SearchTree()
      reads this, Repr()
      requires Valid()
    {
      SearchTreeRec(skeleton)
    }

    function TreeModel(): RB.rbtree
      reads this, elems(skeleton)
    {
      TreeModelRec(skeleton)
    }

    function MapModel(): map<K, V>
      reads this, elems(skeleton)
      requires Valid()
      requires SearchTree()
    {
      RB.toMap(TreeModel())
    }

    method Find(k: K) returns (foundNode: TTNode?)
      requires Valid()
      requires SearchTree()

      ensures foundNode != null <==> k in RB.keys(TreeModel())
      ensures foundNode != null ==> foundNode.key == k
      ensures foundNode != null ==> foundNode.value == RB.Get(TreeModel(), k)

      requires allocated(Repr())
      ensures allocated(Repr())
    /*
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

    predicate ThreadedTree()
      reads this, elems(skeleton)
    {
      RB.ThreadedTreeRoot(TreeModelRec(skeleton))
    }

    predicate RedBlackTree()
      reads this, elems(skeleton)
    {
      RB.RedBlackTreeRoot(TreeModelRec(skeleton))
    }

    // 32"
    method {:verify false} RBInsert(k: K, v: V)
      modifies this, Repr()

      requires Valid()
      requires SearchTree()
      requires ThreadedTree()
      requires RedBlackTree()

      ensures Valid()
      ensures SearchTree()
      ensures ThreadedTree()
      ensures RedBlackTree()
      ensures MapModel() == old(MapModel())[k := v]

      requires allocated(Repr())
      ensures fresh(Repr()-old(Repr()))
      ensures allocated(Repr())
    {
      ghost var z;
      root, skeleton, z := TRBInsertRoot(root, skeleton, k, v);
      TRBi.TRBInsertRootSpec(old(TreeModelRec(skeleton)), k, v);
      TRBi.TRBInsertRootThreaded(old(TreeModelRec(skeleton)), k, v);
      TRBi.TRBInsertRootModel(old(TreeModelRec(skeleton)), k, v);
    }

    /*
    // 45"
    method {:verify false} RBRemove(k: K)
      modifies this, Repr()

      requires Valid()
      requires SearchTree()
      requires RedBlackTree()

      ensures Valid()
      ensures SearchTree()
      ensures RedBlackTree()
      //ensures Model() == old(RB.Remove(Model()))
      ensures MapModel() == old(MapModel()) - {k}

      requires allocated(Repr())
      ensures fresh(Repr()-old(Repr()))
      ensures allocated(Repr())
    {
      ghost var z;
      root, skeleton, z := RemoveRoot(root, skeleton, k);
      RBr.RemoveRootSpec(old(TreeModelRec(skeleton)), k);
      RBr.RemoveRootModel(old(TreeModelRec(skeleton)), k);
    }
    */
  }
}
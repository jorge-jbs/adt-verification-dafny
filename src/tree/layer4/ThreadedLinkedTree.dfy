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
      && (node != null ==> node in elems(parent.skeleton))
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

    static function SkGetP(node: TTNode, root: TTNode?, rootSk: ttreePointer<TTNode>): ttree<TTNode>
      reads elemsP(rootSk)
      requires ValidRecP(root, rootSk, false) || ValidRecP(root, rootSk, true)
      requires node in elemsP(rootSk)
      requires TRB.PointerSearchTree(TreeModelRecP(rootSk))
      ensures ValidRec(node, SkGetP(node, root, rootSk))
      ensures node.key in TRB.pointerKeys(TreeModelRecP(rootSk))
      ensures TreeModelRec(SkGetP(node, root, rootSk)) == TRB.PointerGetSubtree(TreeModelRecP(rootSk), node.key)
    {
      match rootSk {
        case Child(_) => SkGet(node, root, rootSk.child)
      }
    }

    static function SkGet(node: TTNode, root: TTNode?, rootSk: ttree<TTNode>): ttree<TTNode>
      reads elems(rootSk)
      requires ValidRec(root, rootSk)
      requires node in elems(rootSk)
      requires TRB.SearchTree(TreeModelRec(rootSk))
      ensures ValidRec(node, SkGet(node, root, rootSk))
      ensures node.key in TRB.keys(TreeModelRec(rootSk))
      ensures TreeModelRec(SkGet(node, root, rootSk)) == TRB.GetSubtree(TreeModelRec(rootSk), node.key)
    {
      if node in elemsP(rootSk.left) then
        SkGetP(node, root.left, rootSk.left)
      else if node in elemsP(rootSk.right) then
        SkGetP(node, root.right, rootSk.right)
      else
        rootSk
    }

    static method MinP(node: TTNode, ghost sk: ttreePointer<TTNode>)
        returns (newNode: TTNode, ghost newSk: ttree<TTNode>)
      requires ValidRecP(node, sk, false)
      ensures ValidRec(newNode, newSk)
      ensures TreeModelRec(newSk)
        == TRB.minSubtreeP(TreeModelRecP(sk))
      ensures newNode in elemsP(sk)
      ensures T.SubtreeP(newSk, sk)
      ensures TRB.PointerSubtree(TreeModelRec(newSk), TreeModelRecP(sk))

      requires allocated(elemsP(sk))
      ensures allocated(elemsP(sk))
      ensures allocated(elems(newSk))
    {
      newNode, newSk := Min(node, sk.child);
    }

    static method {:verify false} Min(node: TTNode, ghost sk: ttree<TTNode>)
        returns (newNode: TTNode, ghost newSk: ttree<TTNode>)
      requires ValidRec(node, sk)
      ensures ValidRec(newNode, newSk)
      ensures newNode in elems(sk)
      ensures T.Subtree(newSk, sk)
      ensures TreeModelRec(newSk)
        == TRB.minSubtree(TreeModelRec(sk))

      requires allocated(elems(sk))
      ensures allocated(elems(sk))
      ensures allocated(elems(newSk))
    {
      if node.left != null && !node.isThreadLeft {
        newNode, newSk := MinP(node.left, sk.left);
      } else {
        newNode, newSk := node, sk;
      }
    }

    method Next()
      modifies this
      requires Valid()
      requires HasPeek()
      requires parent.Valid()
      requires parent.SearchTree()
      requires parent.Threaded()
      ensures Valid()
      ensures ItModel() == TRBit.Next(old(ItModel()), old(parent.TreeModel()))

      requires allocated(elems(sk))
      requires allocated(parent.Repr())
      ensures allocated(elems(sk))
      ensures allocated(parent.Repr())
    {
      assert node != null;
      if node.isThreadRight {
        assume false;
        assert ValidRecP(node.right, sk.right, node.isThreadRight);
        assert TreeModelRecP(sk.right).Thread?;
        assert node.right != null;
        assert node.right in elems(parent.skeleton) by {
          assert node.right in elemsAndThreadsP(sk.right);
          calc {
            elemsAndThreadsP(sk.right);
            <= elemsAndThreads(sk);
            <= {parent.SubtreeOfInElems(node, sk);} elemsAndThreads(parent.skeleton);
            == {parent.ElemsOfThread();} elems(parent.skeleton);
          }
        }
        node := node.right;
        sk := SkGet(node, parent.root, parent.skeleton);
        assume allocated(sk);
        assume allocated(parent.Repr());
        assume false;
        /*
        calc == {
          ItModel();
          TRBit.Link(TreeModelRec(SkGet'(node, parent.root, parent.skeleton)));
          TRBit.Link(TreeModelRec(SkGet'(node, parent.root, parent.skeleton)));
          TRBit.Link(TRB.GetSubtree(TreeModelRec(parent.skeleton), node.key));
          { assert TreeModelRec(parent.skeleton) == old(parent.TreeModel()); }
          TRBit.Link(TRB.GetSubtree(old(parent.TreeModel()), node.key));
          { assert node.key == old(node.right.key); }
          TRBit.Link(TRB.GetSubtree(old(parent.TreeModel()), old(node.right.key)));
          TRBit.Next(old(ItModel()), old(parent.TreeModel()));
        }
        */
      } else if node.right == null {
        //assume false;
        assert ValidRecP(node.right, sk.right, node.isThreadRight);
        assert TreeModelRecP(sk.right) == TRB.Child(TRB.Empty());
        node := null;
        sk := Empty;
        isPastTheEnd := true;
      } else {
        //assume false;
        ghost var oldSk := sk;
        assert TRB.Subtree(TreeModelRec(oldSk), parent.TreeModel());
        assert oldSkInSkeleton: elemsAndThreads(oldSk) <= elems(parent.skeleton) by {
          calc {
            elemsAndThreads(oldSk);
            <= {parent.SubtreeOfInElems(node, oldSk);} elemsAndThreads(parent.skeleton);
            == {parent.ElemsOfThread();} elems(parent.skeleton);
          }
        }
        node, sk := MinP(node.right, sk.right);
        assert TRB.Subtree(TreeModelRec(sk), parent.TreeModel()) by {
          //assume false;
          assert TRB.PointerSubtree(TreeModelRec(sk), TreeModelRecP(oldSk.right));
          assert TRB.Subtree(TreeModelRec(sk), TreeModelRec(oldSk));
          assert TRB.Subtree(TreeModelRec(oldSk), parent.TreeModel());
          TRB.SubtreeTrans(TreeModelRec(sk), TreeModelRec(oldSk), parent.TreeModel());
        }
        assert node in elems(parent.skeleton) by {
          //assume false;
          assert node in elemsAndThreads(sk);
          calc {
            elemsAndThreads(sk);
            <= elemsAndThreadsP(oldSk.right);
            <= elemsAndThreads(oldSk);
            <= {reveal oldSkInSkeleton;} elems(parent.skeleton);
          }
        }
        assert ValidRec(node, sk);
        assert TRBit.Valid(ItModel(), parent.TreeModel()) by {
          //assume false;
        }
        assert Valid();
        assert TreeModelRec(sk)
          == TRB.minSubtreeP(old(TreeModelRecP(sk.right)));
        assert ItModel() == TRBit.Link(TRB.minSubtreeP(old(TreeModelRecP(sk.right))));
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

    predicate Threaded()
      reads this, Repr()
      requires Valid()
    {
      ThreadedRoot(root, skeleton)
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

    lemma ElemsOfThread()
      requires Valid()
      requires Threaded()
      ensures elems(skeleton) == elemsAndThreads(skeleton)
    {
      ElemsOfThreadRoot(root, skeleton);
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
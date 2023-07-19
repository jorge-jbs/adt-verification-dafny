include "../../../src/MUtils.dfy"
include "../../../src/tree/layer1/OrderedSetUtils.dfy"
include "../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../src/tree/layer4/TRBTree/Iterator.dfy"
include "../../../src/tree/layer4/TRBTree/TRBInsert.dfy"
include "../../../src/tree/layer4/TTree.dfy"
include "../../../src/tree/KeyValue.dfy"
include "../../../src/tree/layer4/TTNode.dfy"
include "../../../src/tree/layer4/ThreadedLinkedTree/TRBInsert.dfy"
include "../../../src/tree/layer4/ThreadedLinkedTree/Min.dfy"
include "../../../src/MUtils.dfy"

module ThreadedLinkedTree {
  import opened Utils
  import opened TTNode
  import TRB = TRBTree.Base
  import TRBi = TRBTree.TRBInsert
  import TRBit = TRBTree.Iterator
  import opened T = TTree
  import opened KeyValue
  import opened TRBInsert
  import opened Min
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

    method {:verify false} Next()  // 3'
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
        sk := GetSk(node, parent.root, parent.skeleton);
        Allocated(elems(sk));
      } else if node.right == null {
        assert ValidRecP(node.right, sk.right, node.isThreadRight);
        assert TreeModelRecP(sk.right) == TRB.Child(TRB.Empty());
        node := null;
        sk := Empty;
        isPastTheEnd := true;
      } else {
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
        assert Valid() by {
          assert TRB.Subtree(TreeModelRec(sk), parent.TreeModel()) by {
            assert TRB.SubtreeP(TreeModelRec(sk), TreeModelRecP(oldSk.right));
            assert TRB.Subtree(TreeModelRec(sk), TreeModelRec(oldSk));
            assert TRB.Subtree(TreeModelRec(oldSk), parent.TreeModel());
            TRB.SubtreeTrans(TreeModelRec(sk), TreeModelRec(oldSk), parent.TreeModel());
          }
          assert node in elems(parent.skeleton) by {
            assert node in elemsAndThreads(sk);
            calc {
              elemsAndThreads(sk);
              <= elemsAndThreadsP(oldSk.right);
              <= elemsAndThreads(oldSk);
              <= {reveal oldSkInSkeleton;} elems(parent.skeleton);
            }
          }
          assert ValidRec(node, sk);
          assert TRBit.Valid(ItModel(), parent.TreeModel());
        }
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
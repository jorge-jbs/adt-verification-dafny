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
    ghost var sk: ttree<TTNode>
    ghost var isPastTheEnd: bool
    ghost var parent: ThreadedLinkedTree

    ghost function ItModel(): TRBit.iter
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

    ghost predicate Valid()
      reads this, elems(sk), parent, parent.Repr()
    {
      && (node != null ==> node in elems(parent.skeleton))
      && ValidRec(node, sk)
      && TRBit.Valid(ItModel(), parent.Model())
    }

    constructor Root(parent: ThreadedLinkedTree)
    {
      this.node := parent.root;
      this.sk := parent.skeleton;
      this.isPastTheEnd := false;
      this.parent := parent;
    }

    ghost function Index(): int
      reads this, node, elems(sk), parent, elems(parent.skeleton)
      requires ValidRec(node, sk)
    {
      TRBit.Index(ItModel(), parent.Model())
    }

    ghost predicate HasPeek()
      reads this, node, elems(sk)
      requires ValidRec(node, sk)
    {
      TRBit.HasPeek(ItModel())
    }

    ghost function Peek(): (K, V)
      reads this, node, elems(sk), parent, elems(parent.skeleton)
      requires ValidRec(node, sk)
      requires HasPeek()
    {
      TRBit.Peek(ItModel(), parent.Model())
    }

    method {:verify false} Next()  // 62"
      modifies this
      requires Valid()
      requires HasPeek()
      requires parent.Valid()
      requires parent.Threaded()
      requires parent.SearchTree()
      ensures Valid()
      ensures ItModel() == TRBit.Next(old(ItModel()), old(parent.Model()))

      requires allocated(elems(sk))
      requires allocated(parent.Repr())
      ensures allocated(elems(sk))
      ensures allocated(parent.Repr())
    {
      if node.right == null {
        assert ValidRec(node.right, sk.right);
        assert sk.right.Empty?;
        assert TreeModelRec(sk).right.Empty?;
        assert ItModel().link.right.Empty?;
        node := null;
        sk := Empty;
        isPastTheEnd := true;
      } else if node.isThreadRight {
        assert ValidChild(node.right, sk.right, true);
        assert sk.right.Thread?;
        assert TreeModelRec(sk).right.Thread?;
        assert ItModel().link.right.Thread?;
        assert node.right in elems(parent.skeleton) by {
          assert node.right in elemsAndThreads(sk);
          calc {
            elemsAndThreads(sk);
            <= {parent.SubtreeOfInElems(node, sk);} elemsAndThreads(parent.skeleton);
            == {parent.ElemsOfThread();} elems(parent.skeleton);
          }
          
        }
        sk := GetSk(node.right, parent.root, parent.skeleton);
        node := node.right;
        assert ItModel() == TRBit.Next(old(ItModel()), old(parent.Model())) by {
          calc == {
            TRBit.Next(old(ItModel()), old(parent.Model()));
            TRBit.Link(TRB.GetSubtree(old(parent.Model()), old(TreeModelRec(sk).right.thread)));
            TRBit.Link(TRB.GetSubtree(old(parent.Model()), old(node.right.key)));
            ItModel();
          }
        }
      } else {
        TRBit.NextSpec(ItModel(), parent.Model());
        assert ValidRec(node.right, sk.right);
        assert sk.right.Node?;
        assert TreeModelRec(sk).right.Node?;
        assert ItModel().link.right.Node?;
        assert node.right in elems(sk);
        assert elems(sk) <= elems(parent.skeleton) by {
          calc {
            elems(sk);
            <= {ElemsInElemsAndThreads(sk);} elemsAndThreads(sk);
            <= {parent.SubtreeOfInElems(node, sk);} elemsAndThreads(parent.skeleton);
            == {parent.ElemsOfThread();} elems(parent.skeleton);
          }
        }
        parent.ElemsOfThread();
        node, sk := Min.Min(node.right, sk.right);
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

    method Insert(k: K, v: V)
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

      requires allocated(Repr())
      ensures fresh(Repr()-old(Repr()))
      ensures allocated(Repr())
    {
      TRBi.TRBInsertRootSpec(TreeModelRec(skeleton), k, v);
      ghost var z;
      root, skeleton, z := TRBInsertRoot(root, skeleton, k, v);
    }

    method Remove(k: K)
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

      requires allocated(Repr())
      ensures fresh(Repr()-old(Repr()))
      ensures allocated(Repr())
    {
      TRBr.RemoveRootSpec(TreeModelRec(skeleton), k);
      root, skeleton := R.RemoveRoot(root, skeleton, k);
    }
  }

  method {:main} TestThreadedLinkedTree()
  {
    var t := new ThreadedLinkedTree();
    t.Insert(1, 0);
  }
}
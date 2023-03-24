include "../../../src/MUtils.dfy"
include "../../../src/tree/alt-layer4/RBTree/Base.dfy"
include "../../../src/tree/alt-layer4/RBTree/SInsert.dfy"
include "../../../src/tree/alt-layer4/RBTree/RBInsert.dfy"
include "../../../src/tree/alt-layer4/RBTree/Iterator.2.dfy"
include "../../../src/tree/alt-layer4/Tree.dfy"
include "../../../src/tree/alt-layer4/KeyValue.dfy"
include "../../../src/tree/alt-layer4/TNode.dfy"
include "../../../src/tree/alt-layer4/LinkedTree/SInsert.dfy"
include "../../../src/tree/alt-layer4/LinkedTree/RBInsert.dfy"
include "../../../src/tree/alt-layer4/LinkedTree/RBRemove.dfy"
//include "../../../src/MUtils.dfy"

module LinkedTree {
  import opened Utils
  import opened TNode
  import RB = RBTree.Base
  import RBi = RBTree.RBInsert
  import RBr = RBTree.RBRemove
  import RBs = RBTree.SInsert
  import RBit = RBTree.Iterator
  import opened T = Tree
  import opened KeyValue
  import opened SInsert
  import opened RBInsert
  import opened RBRemove

  class Iterator {
    var stack: seq<TNode>;
    ghost var stackSk: seq<tree<TNode>>;
    ghost var parent: LinkedTree;
    ghost var traversed: seq<(K, V)>;

    function Parent(): LinkedTree
      reads this
    {
      parent
    }

    function RBStack(): seq<RB.rbtree>
      reads this, BigUnion(set sk | sk in stackSk :: elems(sk))
    {
      seq(|stackSk|, i reads this, BigUnion(set sk | sk in stackSk :: elems(sk)) requires 0 <= i < |stackSk| => TreeModelRec(stackSk[i]))
    }

    predicate Valid()
      reads this, parent, elems(parent.skeleton), BigUnion(set sk | sk in stackSk :: elems(sk))
    {
      && RBit.ValidStack(RBStack())
      && RB.inorder(TreeModelRec(parent.skeleton)) == traversed + RBit.inorderStack(RBStack())
    }


    constructor(node: TNode, ghost sk: tree<TNode>, ghost parent: LinkedTree)
    {
      this.stack := [node];
      this.stackSk := [sk];
      this.parent := parent;
      this.traversed := [];
    }

    lemma DescendAndPushInd(st: seq<RB.rbtree>, node: RB.rbtree)
      requires node.Node?
      ensures RBit.DescendAndPush(st + [node], node.left) == RBit.DescendAndPush(st, node)
    {}

    method DescendAndPush(node: TNode?, ghost sk: tree<TNode>)
      modifies this, Parent(), Parent().Repr()
      requires ValidRec(node, sk)
      //requires Valid()
      requires RBit.ValidStack(RBStack())
      ensures RBit.ValidStack(RBStack())
      ensures RBStack() == RBit.DescendAndPush(old(RBStack()), old(TreeModelRec(sk)))

      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())
    {
      if node != null {
        TreeModelRecChildren(sk);
        ghost var st := RBStack();
        assert forall k | 0 <= k < |st| :: st[k].Node?;
        assert forall k | 0 <= k < |stackSk| :: st[k] == TreeModelRec(stackSk[k]);
        stack := stack + [node];
        stackSk := stackSk + [sk];
        st := RBStack();
        assert RBStack() == st == old(RBStack()) + [TreeModelRec(sk)];
        assert RBStack() == st == old(RBStack()) + [old(TreeModelRec(sk))];
        assert forall k | 0 <= k < |stackSk| :: st[k] == TreeModelRec(stackSk[k]);
        assert forall k | 0 <= k < |stackSk| :: TreeModelRec(stackSk[k]).Node?;
        assert forall k | 0 <= k < |st| :: st[k].Node?;
        DescendAndPush(node.left, sk.left);
        assert RBStack() == RBit.DescendAndPush(st, old(TreeModelRec(sk.left)));
        assume old(TreeModelRec(sk.left)) == old(TreeModelRec(sk)).left;
        assume false;
        assert RBStack() == RBit.DescendAndPush(st, old(TreeModelRec(sk).left));
        assert st == old(RBStack()) + [old(TreeModelRec(sk))];
        DescendAndPushInd(old(RBStack()), old(TreeModelRec(sk)));
        assert RBit.ValidStack(RBStack());
        assume false;
        assert RBStack() == RBit.DescendAndPush(old(RBStack()), old(TreeModelRec(sk)));
      } else {
      }
    }

/*
    method DescendAndPush(node: TNode?, ghost sk: tree<TNode>)
      modifies this, Parent(), Parent().Repr()
      requires ValidRec(node, sk)
      requires Valid()

      requires allocated(Parent())
      requires allocated(Parent().Repr())
      ensures fresh(Parent().Repr() - old(Parent().Repr()))
      ensures allocated(Parent().Repr())
    {
      ghost var oldStack := RBStack();
      ghost var oldNode := TreeModelRec(sk);
      var node := node;
      ghost var sk := sk;
      while node != null
        decreases sk
        invariant ValidRec(node, sk)
        invariant RBit.ValidStack(RBStack())
        //invariant RBStack() <= RBit.DescendAndPush(oldStack, oldNode)
        //invariant RB.inorder(TreeModelRec(skeleton)) == traversed + RBit.inorderStack(RBStack())
        invariant allocated(this)
        invariant allocated(Parent())
        invariant allocated(Parent().Repr())
        invariant fresh(Parent().Repr() - old(Parent().Repr()))
      {
        var st := RBStack();
        label init:
        assert RBit.ValidStack(st);
        assert forall k | 0 <= k < |st| :: st[k].Node?;
        assert forall k | 0 <= k < |stackSk| :: st[k] == TreeModelRec(stackSk[k]);
        stack := stack + [node];
        stackSk := stackSk + [sk];
        st := RBStack();
        assert node != null;
        assert sk.Node?;
        assert TreeModelRec(sk).Node?;
        assert forall k | 0 <= k < |stackSk| :: st[k] == TreeModelRec(stackSk[k]);
        assert forall k | 0 <= k < |stackSk| :: TreeModelRec(stackSk[k]).Node?;
        assert forall k | 0 <= k < |st| :: st[k].Node?;
        node := node.left;
        sk := sk.left;
      }
    }
  */
  }

  class LinkedTree {
    var root: TNode?;
    ghost var skeleton: tree<TNode>;

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
      RB.model(TreeModel())
    }

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

    predicate RedBlackTree()
      reads this, elems(skeleton)
    {
      RB.RedBlackTreeRoot(TreeModelRec(skeleton))
    }

    // 26"
    method {:verify false} RBInsert(k: K, v: V)
      modifies this, Repr()

      requires Valid()
      requires SearchTree()
      requires RedBlackTree()

      ensures Valid()
      ensures SearchTree()
      ensures RedBlackTree()
      ensures MapModel() == old(MapModel())[k := v]

      requires allocated(Repr())
      ensures fresh(Repr()-old(Repr()))
      ensures allocated(Repr())
    {
      ghost var z;
      root, skeleton, z := RBInsertRoot(root, skeleton, k, v);
      RBi.RBInsertRootSpec(old(TreeModelRec(skeleton)), k, v);
      RBi.RBInsertRootModel(old(TreeModelRec(skeleton)), k, v);
    }

    // 45"
    method {:verify false} RBRemove(k: K)
      modifies this, Repr()

      requires Valid()
      requires SearchTree()
      requires RedBlackTree()

      ensures Valid()
      ensures SearchTree()
      ensures RedBlackTree()
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
  }
}
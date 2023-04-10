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

    static function RBStackRec(stack: seq<tree<TNode>>): seq<RB.rbtree>
      reads BigUnion(set sk | sk in stack :: elems(sk))
      requires forall i | 0 <= i < |stack| :: stack[i].Node?
      ensures RBit.ValidStack(RBStackRec(stack))
      ensures |stack| == |RBStackRec(stack)|
      ensures forall i | 0 <= i < |stack| :: RBStackRec(stack)[i] == TreeModelRec(stack[i])
    {
      if stack == [] then
        []
      else
        [TreeModelRec(stack[0])] + RBStackRec(stack[1..])
    }

    static lemma RBStackRecLast(stack: seq<tree<TNode>>, sk: tree<TNode>)
      requires forall i | 0 <= i < |stack| :: stack[i].Node?
      requires sk.Node?
      ensures RBStackRec(stack + [sk]) == RBStackRec(stack) + [TreeModelRec(sk)]
    {}

    function RBStack(): seq<RB.rbtree>
      reads this, BigUnion(set sk | sk in stackSk :: elems(sk))
      requires forall i | 0 <= i < |stackSk| :: stackSk[i].Node?
    {
      RBStackRec(stackSk)
    }

    predicate Valid()
      reads this, parent, elems(parent.skeleton), BigUnion(set sk | sk in stackSk :: elems(sk))
    {
      && |stack| == |stackSk|
      && (forall i | 0 <= i < |stack| :: ValidRec(stack[i], stackSk[i]))
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

    static lemma DescendAndPushInd(st: seq<RB.rbtree>, node: RB.rbtree)
      requires node.Node?
      ensures RBit.DescendAndPush(st + [node], node.left) == RBit.DescendAndPush(st, node)
    {}

    static method DescendAndPush(
        node: TNode?,
        ghost sk: tree<TNode>,
        stack: seq<TNode>,
        ghost stackSk: seq<tree<TNode>>
      )
      returns (
        newStack: seq<TNode>,
        ghost newStackSk: seq<tree<TNode>>
      )
      requires ValidRec(node, sk)
      requires |stack| == |stackSk|
      requires forall i | 0 <= i < |stack| :: ValidRec(stack[i], stackSk[i])
      requires RBit.ValidStack(RBStackRec(stackSk))

      ensures |newStack| == |newStackSk|
      ensures forall i | 0 <= i < |newStack| :: ValidRec(newStack[i], newStackSk[i])
      ensures RBit.ValidStack(RBStackRec(newStackSk))
      ensures RBStackRec(newStackSk) == RBit.DescendAndPush(RBStackRec(stackSk), TreeModelRec(sk))

      requires allocated(elems(sk))
      requires forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]))
      ensures forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]))
    {
      if node != null {
        newStack, newStackSk := DescendAndPush(node.left, sk.left, stack + [node], stackSk + [sk]);
        //RBStackRecLast(stackSk, sk);  // This is the only line needed to automatically prove the postconditions
        calc == {
          RBStackRec(newStackSk);
          RBit.DescendAndPush(RBStackRec(stackSk + [sk]), TreeModelRec(sk.left));
          { RBStackRecLast(stackSk, sk); }
          RBit.DescendAndPush(RBStackRec(stackSk) + [TreeModelRec(sk)], TreeModelRec(sk.left));
          { TreeModelRecChildren(sk); }
          RBit.DescendAndPush(RBStackRec(stackSk) + [TreeModelRec(sk)], TreeModelRec(sk).left);
        }
        DescendAndPushInd(RBStackRec(stackSk), TreeModelRec(sk));
      } else {
        newStack := stack;
        newStackSk := stackSk;
      }
    }
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
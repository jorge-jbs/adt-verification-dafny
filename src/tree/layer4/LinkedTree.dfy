include "../../../src/MUtils.dfy"
include "../../../src/tree/layer4/RBTree/Base.dfy"
include "../../../src/tree/layer4/RBTree/SInsert.dfy"
include "../../../src/tree/layer4/RBTree/RBInsert.dfy"
include "../../../src/tree/layer4/RBTree/Iterator.2.dfy"
include "../../../src/tree/layer4/Tree.dfy"
include "../../../src/tree/layer4/KeyValue.dfy"
include "../../../src/tree/layer4/TNode.dfy"
include "../../../src/tree/layer4/LinkedTree/Find.dfy"
include "../../../src/tree/layer4/LinkedTree/SInsert.dfy"
include "../../../src/tree/layer4/LinkedTree/RBInsert.dfy"
include "../../../src/tree/layer4/LinkedTree/RBRemove.dfy"
include "../../../src/MUtils.dfy"

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
  import opened Find
  import opened SInsert
  import opened RBInsert
  import opened RBRemove

  class LinkedTreeIterator {
    var stack: seq<TNode>;
    ghost var stackSk: seq<tree<TNode>>;
    ghost var parent: LinkedTree;
    ghost var traversed: seq<(K, V)>;

    function Parent(): LinkedTree
      reads this
    {
      parent
    }

    static function RBStackRec(stackSk: seq<tree<TNode>>): seq<RB.rbtree>
      reads BigUnion(set sk | sk in stackSk :: elems(sk))
      //reads set sk, n | sk in stackSk && n in elems(sk) :: n//elems(sk)
      requires forall i | 0 <= i < |stackSk| :: stackSk[i].Node?
      ensures RBit.ValidStack(RBStackRec(stackSk))
      ensures |stackSk| == |RBStackRec(stackSk)|
      ensures forall i | 0 <= i < |stackSk| :: RBStackRec(stackSk)[i] == TreeModelRec(stackSk[i])
    {
      seq(|stackSk|, i requires 0 <= i < |stackSk| reads BigUnion(set sk | sk in stackSk :: elems(sk)) => TreeModelRec(stackSk[i]))
      /*
      if stackSk == [] then
        []
      else
        [TreeModelRec(stackSk[0])] + RBStackRec(stackSk[1..])
        */
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
      && (forall sk | sk in stackSk :: elems(sk) <= elems(parent.skeleton))
      && RBit.ValidStack(RBStack())
      && RB.inorder(TreeModelRec(parent.skeleton)) == traversed + RBit.inorderStack(RBStack())
    }

    lemma TraversedInModel()
      ensures forall p | p in traversed :: p.0 in RB.keys(TreeModelRec(parent.skeleton))

    constructor(node: TNode, ghost sk: tree<TNode>, ghost parent: LinkedTree)
    {
      this.stack := [node];
      this.stackSk := [sk];
      this.parent := parent;
      this.traversed := [];
    }

    static method FirstAux(
        parent: LinkedTree,
        ghost traversed: seq<(K, V)>,
        stack: seq<TNode>,
        ghost stackSk: seq<tree<TNode>>
      )
      returns (
        newStack: seq<TNode>,
        ghost newStackSk: seq<tree<TNode>>
      )
      requires parent.Valid()
      requires traversed == []
      requires stack == []
      requires stackSk == []

      ensures |newStack| == |newStackSk|
      ensures (forall i | 0 <= i < |newStack| :: ValidRec(newStack[i], newStackSk[i]))
      ensures (forall sk | sk in newStackSk :: elems(sk) <= elems(parent.skeleton))
      ensures RBit.ValidStack(RBStackRec(newStackSk))
      ensures RB.inorder(TreeModelRec(parent.skeleton)) == traversed + RBit.inorderStack(RBStackRec(newStackSk))

      requires allocated(parent.Repr())
      ensures allocated(parent.Repr())
      requires forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]))
      ensures forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]))
      ensures forall i | 0 <= i < |newStackSk| :: allocated(elems(newStackSk[i]))
    {
      assert RBit.ValidStack(RBStackRec([]));
      assert RB.inorder(TreeModelRec(parent.skeleton)) == traversed + RB.inorder(TreeModelRec(parent.skeleton)) + RBit.inorderStack(RBStackRec([]));
      RBit.DescendAndPushSpec(TreeModelRec(parent.skeleton), RBStackRec([]), TreeModelRec(parent.skeleton), []);
      newStack, newStackSk := DescendAndPush(parent.root, parent.skeleton, [], [], parent.skeleton);
    }

    constructor {:verify false} First(parent: LinkedTree)  // 33"
      requires parent.Valid()
      ensures Valid()
      ensures this.parent == parent
      ensures traversed == []

      requires allocated(parent.Repr())
      ensures allocated(parent.Repr())
      ensures forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]))
    {
      this.parent := parent;
      traversed := [];
      stack := [];
      stackSk := [];
      new;
      stack, stackSk := FirstAux(parent, traversed, stack, stackSk);
    }

    static lemma DescendAndPushInd(st: seq<RB.rbtree>, node: RB.rbtree)
      requires node.Node?
      ensures RBit.DescendAndPush(st + [node], node.left) == RBit.DescendAndPush(st, node)
    {}

    static method DescendAndPush(
        node: TNode?,
        ghost sk: tree<TNode>,
        stack: seq<TNode>,
        ghost stackSk: seq<tree<TNode>>,
        ghost parentSkeleton: tree<TNode>
      )
      returns (
        newStack: seq<TNode>,
        ghost newStackSk: seq<tree<TNode>>
      )
      requires ValidRec(node, sk)
      requires |stack| == |stackSk|
      requires forall i | 0 <= i < |stack| :: ValidRec(stack[i], stackSk[i])
      requires elems(sk) <= elems(parentSkeleton)
      requires forall sk | sk in stackSk :: elems(sk) <= elems(parentSkeleton)
      requires RBit.ValidStack(RBStackRec(stackSk))

      ensures |newStack| == |newStackSk|
      ensures forall i | 0 <= i < |newStack| :: ValidRec(newStack[i], newStackSk[i])
      ensures forall sk | sk in newStackSk :: elems(sk) <= elems(parentSkeleton)
      ensures RBit.ValidStack(RBStackRec(newStackSk))
      ensures RBStackRec(newStackSk) == RBit.DescendAndPush(RBStackRec(stackSk), TreeModelRec(sk))

      requires allocated(elems(sk))
      ensures allocated(elems(sk))
      requires forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]))
      ensures forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]))
      ensures forall i | 0 <= i < |newStackSk| :: allocated(elems(newStackSk[i]))
    {
      if node != null {
        newStack, newStackSk := DescendAndPush(node.left, sk.left, stack + [node], stackSk + [sk], parentSkeleton);
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

    static lemma RBStackSub(stackSk: seq<tree<TNode>>)
      requires stackSk != []
      requires forall i | 0 <= i < |stackSk| :: stackSk[i].Node?
      ensures RBStackRec(stackSk[..|stackSk|-1]) == RBStackRec(stackSk)[..|RBStackRec(stackSk)|-1]
    {
      if |stackSk| == 1 {
      } else {
        RBStackSub(stackSk[1..]);
      }
    }

    static method {:verify true} NextAux(
        stack: seq<TNode>,
        ghost stackSk: seq<tree<TNode>>,
        ghost parentSkeleton: tree<TNode>,
        ghost traversed: seq<(K, V)>
      )
      returns (
        newStack: seq<TNode>, ghost newStackSk: seq<tree<TNode>>,
        ghost newTraversed: seq<(K, V)>,
        k: K, v: V
      )

      requires |stack| == |stackSk|
      requires forall i | 0 <= i < |stack| :: ValidRec(stack[i], stackSk[i])
      requires forall sk | sk in stackSk :: elems(sk) <= elems(parentSkeleton)
      requires RBit.ValidStack(RBStackRec(stackSk))
      requires RBStackRec(stackSk) != []
      requires RB.inorder(TreeModelRec(parentSkeleton)) == traversed + RBit.inorderStack(RBStackRec(stackSk));

      ensures |newStack| == |newStackSk|
      ensures forall i | 0 <= i < |newStack| :: ValidRec(newStack[i], newStackSk[i])
      ensures forall sk | sk in newStackSk :: elems(sk) <= elems(parentSkeleton)
      ensures RBit.ValidStack(RBStackRec(newStackSk))
      ensures RBStackRec(newStackSk) == RBit.Next(RBStackRec(stackSk))
      ensures k == stack[|stack|-1].key == TreeModelRec(stackSk[|stackSk|-1]).key
      ensures v == stack[|stack|-1].value == TreeModelRec(stackSk[|stackSk|-1]).value
      ensures RB.inorder(TreeModelRec(parentSkeleton)) == traversed + [(k, v)] + RBit.inorderStack(RBStackRec(newStackSk));
      ensures RB.inorder(TreeModelRec(parentSkeleton)) == newTraversed + RBit.inorderStack(RBStackRec(newStackSk));

      requires allocated(elems(parentSkeleton))
      requires forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]))
      ensures allocated(elems(parentSkeleton))
      ensures forall i | 0 <= i < |newStackSk| :: allocated(elems(newStackSk[i]))
    {
      var node := stack[|stack|-1];
      k, v := node.key, node.value;
      ghost var skeleton := stackSk[|stackSk|-1];
      newStack, newStackSk := DescendAndPush(node.right, skeleton.right, stack[..|stack|-1], stackSk[..|stackSk|-1], parentSkeleton);
      calc == {
        RBStackRec(newStackSk);
        RBit.DescendAndPush(RBStackRec(stackSk[..|stackSk|-1]), TreeModelRec(skeleton.right));
        RBit.DescendAndPush(RBStackRec(stackSk[..|stackSk|-1]), RBStackRec(stackSk)[|stackSk|-1].right);
        { RBStackSub(stackSk); }
        RBit.DescendAndPush(RBStackRec(stackSk)[..|RBStackRec(stackSk)|-1], RBStackRec(stackSk)[|RBStackRec(stackSk)|-1].right);
        RBit.Next(RBStackRec(stackSk));
      }
      RBit.NextSpec(TreeModelRec(parentSkeleton), RBStackRec(stackSk), traversed);
      newTraversed := traversed + [(k, v)];
    }

    method {:verify false} Next() returns (k: K, v: V)  // 5'10"
      modifies this
      requires Valid()
      requires RBit.ValidStack(RBStack())  /* redundant */
      requires RBStack() != []
      ensures Valid()
      ensures RBStack() == old(RBit.Next(RBStack()))

      requires allocated(elems(parent.skeleton));
      requires forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]));
      ensures allocated(elems(parent.skeleton));
      ensures forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]))
    {
      assert RBStackRec(stackSk) == old(RBStackRec(stackSk));
      stack, stackSk, traversed, k, v := NextAux(stack, stackSk, parent.skeleton, traversed);
    }
  }

  class {:verify false} LinkedTree {
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
      RB.model(TreeModel())
    }

    method Find(k: K) returns (foundNode: TNode?)
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
  }
}
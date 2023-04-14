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
      ensures allocated(elems(sk))
      requires forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]))
      ensures forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]))
      ensures forall i | 0 <= i < |newStackSk| :: allocated(elems(newStackSk[i]))
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

    static method Works(s: set<TNode>)
      modifies {}
    {
      assert unchanged(s);
    }

    static method {:verify false} DoesntWorkSadFace(t: tree<TNode>)
      modifies {}
    {
      assert unchanged(elems(t));
    }

    static method {:verify false} DoesntWorkNeitherSadFace(node: TNode, sk: tree<TNode>)
      modifies {}
      requires ValidRec(node, sk)
      //requires allocated(elems(sk))
    {
      assert unchanged(elems(sk));
    }

    static method NowItWorksYayHappyFace(sk: tree<TNode>)
      modifies {}
      requires allocated(elems(sk))
    {
      assert unchanged(elems(sk));
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

    /*
    static method NextAux(
        stack: seq<TNode>,
        ghost stackSk: seq<tree<TNode>>,
        ghost parentSkeleton: tree<TNode>,
        ghost traversed: seq<(K, V)>
      )
      returns (
        newStack: seq<TNode>, ghost newStackSk: seq<tree<TNode>>,
        k: K, v: V
      )
      
      requires |stack| == |stackSk|
      requires (forall i | 0 <= i < |stack| :: ValidRec(stack[i], stackSk[i]))
      requires RBit.ValidStack(RBStackRec(stackSk))
      requires RBStackRec(stackSk) != []
      requires RB.inorder(TreeModelRec(parentSkeleton)) == traversed + RBit.inorderStack(RBStackRec(stackSk));

      ensures |newStack| == |newStackSk|
      ensures (forall i | 0 <= i < |newStack| :: ValidRec(newStack[i], newStackSk[i]))
      ensures RBit.ValidStack(RBStackRec(newStackSk))
      ensures RBStackRec(newStackSk) == RBit.Next(RBStackRec(stackSk))
      ensures k == stack[|stack|-1].key == TreeModelRec(stackSk[|stackSk|-1]).key
      ensures v == stack[|stack|-1].value == TreeModelRec(stackSk[|stackSk|-1]).value
      ensures RB.inorder(TreeModelRec(parentSkeleton)) == traversed + [(k, v)] + RBit.inorderStack(RBStackRec(newStackSk));

      requires forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]))
      ensures forall i | 0 <= i < |newStackSk| :: allocated(elems(newStackSk[i]))
    {
      RBit.NextSpec(TreeModelRec(parentSkeleton), RBStackRec(stackSk), traversed);
      var node := stack[|stack|-1];
      k, v := node.key, node.value;
      ghost var skeleton := stackSk[|stackSk|-1];
      calc == {
        RB.inorder(TreeModelRec(parentSkeleton));
        traversed + RBit.inorderStack(RBStackRec(stackSk));
      }
      newStack, newStackSk := DescendAndPush(node.right, skeleton.right, stack[..|stack|-1], stackSk[..|stackSk|-1]);
      calc == {
        RBStackRec(newStackSk);
        RBit.DescendAndPush(RBStackRec(stackSk[..|stackSk|-1]), TreeModelRec(skeleton.right));
        RBit.DescendAndPush(RBStackRec(stackSk[..|stackSk|-1]), RBStackRec(stackSk)[|stackSk|-1].right);
        { RBStackSub(stackSk); }
        RBit.DescendAndPush(RBStackRec(stackSk)[..|RBStackRec(stackSk)|-1], RBStackRec(stackSk)[|RBStackRec(stackSk)|-1].right);
        RBit.Next(RBStackRec(stackSk));
      }
      assume RB.inorder(TreeModelRec(parentSkeleton)) == traversed + [(k, v)] + RBit.inorderStack(RBStackRec(newStackSk));
    }
    */
    
    static method {:verify false} NextAux(
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
      requires (forall i | 0 <= i < |stack| :: ValidRec(stack[i], stackSk[i]))
      requires RBit.ValidStack(RBStackRec(stackSk))
      requires RBStackRec(stackSk) != []
      requires RB.inorder(TreeModelRec(parentSkeleton)) == traversed + RBit.inorderStack(RBStackRec(stackSk));

      ensures |newStack| == |newStackSk|
      ensures (forall i | 0 <= i < |newStack| :: ValidRec(newStack[i], newStackSk[i]))
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
      calc == {
        RB.inorder(TreeModelRec(parentSkeleton));
        traversed + RBit.inorderStack(RBStackRec(stackSk));
      }
      var node := stack[|stack|-1];
      k, v := node.key, node.value;
      ghost var skeleton := stackSk[|stackSk|-1];
      calc == {
        RB.inorder(TreeModelRec(parentSkeleton));
        traversed + RBit.inorderStack(RBStackRec(stackSk));
      }
      newStack, newStackSk := DescendAndPush(node.right, skeleton.right, stack[..|stack|-1], stackSk[..|stackSk|-1]);
      assert unchanged(elems(parentSkeleton));
      assert unchanged(BigUnion(set sk | sk in stackSk :: elems(sk)));
      calc == {
        RB.inorder(TreeModelRec(parentSkeleton));
        traversed + RBit.inorderStack(RBStackRec(stackSk));
      }
      calc == {
        RBStackRec(newStackSk);
        RBit.DescendAndPush(RBStackRec(stackSk[..|stackSk|-1]), TreeModelRec(skeleton.right));
        RBit.DescendAndPush(RBStackRec(stackSk[..|stackSk|-1]), RBStackRec(stackSk)[|stackSk|-1].right);
        { RBStackSub(stackSk); }
        RBit.DescendAndPush(RBStackRec(stackSk)[..|RBStackRec(stackSk)|-1], RBStackRec(stackSk)[|RBStackRec(stackSk)|-1].right);
        RBit.Next(RBStackRec(stackSk));
      }
      calc == {
        RB.inorder(TreeModelRec(parentSkeleton));
        traversed + RBit.inorderStack(RBStackRec(stackSk));
      }
      RBit.NextSpec(TreeModelRec(parentSkeleton), RBStackRec(stackSk), traversed);
      calc == {
        RB.inorder(TreeModelRec(parentSkeleton));
        traversed + [(k, v)] + RBit.inorderStack(RBStackRec(newStackSk));
      }
      newTraversed := traversed + [(k, v)];
    }
    
    method Next() returns (k: K, v: V)  // 21'54"
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
      var newStack;
      ghost var newStackSk, newTraversed;
      newStack, newStackSk, newTraversed, k, v := NextAux(stack, stackSk, parent.skeleton, traversed);
      label PostCall:
      assert RB.inorder(TreeModelRec(parent.skeleton)) == newTraversed + RBit.inorderStack(RBStackRec(newStackSk));
      stack, stackSk := newStack, newStackSk;
      label PostCall2:
      assert |stack| == |stackSk|;
      assert forall i | 0 <= i < |stack| :: ValidRec(stack[i], stackSk[i]);
      assert RBit.ValidStack(RBStack());
      assert unchanged(elems(parent.skeleton));
      assert unchanged@PostCall(BigUnion(set sk | sk in newStackSk :: elems(sk)));
      assert RB.inorder(TreeModelRec(parent.skeleton)) == newTraversed + RBit.inorderStack(RBStackRec(newStackSk));
      assert RB.inorder(TreeModelRec(parent.skeleton)) == newTraversed + RBit.inorderStack(RBStackRec(stackSk));
      //assert RB.inorder(TreeModelRec(parent.skeleton)) == newTraversed + RBit.inorderStack(RBStack());
      assert allocated(elems(parent.skeleton));
      assert forall i | 0 <= i < |newStackSk| :: allocated(elems(stackSk[i]));
      traversed := newTraversed;
      assert |stack| == |stackSk|;
      assert forall i | 0 <= i < |stack| :: ValidRec(stack[i], stackSk[i]);
      assert RBit.ValidStack(RBStack());
      assert unchanged(elems(parent.skeleton));
      assert unchanged@PostCall(BigUnion(set sk | sk in newStackSk :: elems(sk)));
      assert RB.inorder(TreeModelRec(parent.skeleton)) == newTraversed + RBit.inorderStack(RBStackRec(newStackSk));
      assert RB.inorder(TreeModelRec(parent.skeleton)) == newTraversed + RBit.inorderStack(RBStackRec(stackSk));
      assert RB.inorder(TreeModelRec(parent.skeleton)) == traversed + RBit.inorderStack(RBStackRec(stackSk));
    }

/*
    method {:verify false} Next() returns (k: K, v: V)
      modifies this
      requires Valid()
      requires RBit.ValidStack(RBStack())  /* redundant */
      requires RBStack() != []
      ensures Valid()
      //ensures RBStack() == old(RBit.Next(RBStack()))

      requires forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]));
      ensures forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]))
    {
      RBit.NextSpec(TreeModelRec(parent.skeleton), RBStackRec(stackSk), traversed);
      //RBStackSub(stackSk);
      var st := RBStackRec(stackSk);
      assert RB.inorder(TreeModelRec(parent.skeleton)) == traversed + [(st[|st|-1].key, st[|st|-1].value)] + RBit.inorderStack(RBit.Next(st));
      stack, stackSk, k, v := NextAux(stack, stackSk, parent.skeleton, traversed);
      assert |stack| == |stackSk|;
      assert (forall i | 0 <= i < |stack| :: ValidRec(stack[i], stackSk[i]));
      assert RBit.ValidStack(RBStack());
      calc == {
        RB.inorder(TreeModelRec(parent.skeleton));
        { assume false; }
        traversed + [(k, v)] + RBit.inorderStack(RBStack());
      }
      assume false;
      assert RB.inorder(TreeModelRec(parent.skeleton)) == traversed + [(k, v)] + RBit.inorderStack(RBStack());
      assert RB.inorder(TreeModelRec(parent.skeleton)) == traversed + RBit.inorderStack(RBStack());
      assert Valid();
    }
    */

    /*
    method Next()
      modifies this
      requires Valid()
      requires RBit.ValidStack(RBStack())  /* redundant */
      requires RBStack() != []
      ensures Valid()
      //ensures RBStack() == old(RBit.Next(RBStack()))

      requires forall i | 0 <= i < |stackSk| :: allocated(elems(stackSk[i]));
    {
      assert RBit.ValidStack(RBStackRec(stackSk[..|stackSk|-1]));
      ghost var oldStackSk := stackSk;

      var node := stack[|stack|-1];
      ghost var skeleton := stackSk[|stackSk|-1];
      //assume TreeModelRec(skeleton) == RBStack()[|RBStack()|-1];
      var newStack, newStackSk := DescendAndPush(node.right, skeleton.right, stack[..|stack|-1], stackSk[..|stackSk|-1]);
      assert RBStackRec(newStackSk) == RBit.DescendAndPush(RBStackRec(stackSk[..|stackSk|-1]), TreeModelRec(skeleton.right));
      assert RBStackRec(newStackSk) == RBit.DescendAndPush(RBStackRec(oldStackSk[..|oldStackSk|-1]), TreeModelRec(skeleton.right));
      stackSk := newStackSk;
      assume false;
      assert RBStackRec(newStackSk) == RBit.DescendAndPush(RBStackRec(oldStackSk[..|oldStackSk|-1]), TreeModelRec(skeleton.right));
      assume false;
      assert RBStackRec(stackSk) == RBit.DescendAndPush(RBStackRec(oldStackSk[..|oldStackSk|-1]), TreeModelRec(skeleton.right));
      assert |stack| == |stackSk|;
      assert (forall i | 0 <= i < |stack| :: ValidRec(stack[i], stackSk[i]));
      assert RBit.ValidStack(RBStack());
      assume false;
      assert RBStack() == old(RBit.Next(RBStack()));
      assume false;
      assert RB.inorder(TreeModelRec(parent.skeleton)) == traversed + RBit.inorderStack(RBStack());
      assume false;
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
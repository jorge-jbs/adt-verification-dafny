include "../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../src/tree/layer4/TTree1.dfy"
include "../../../src/tree/KeyValue.dfy"
include "../../../src/tree/layer4/Color.dfy"

module TTNode {
  import opened KeyValue
  import opened RB = TRBTree.Base
  import opened T = Tree
  import opened Color

  class TTNode {
    const key: K;
    var value: V;

    var isThreadLeft: bool
    var left: TTNode?;

    var isThreadRight: bool
    var right: TTNode?;
   
    var color: Color;

    constructor(lt: bool, l: TTNode?, k: K, v: V, rt: bool, r: TTNode?, c: Color)
      ensures isThreadLeft == lt
      ensures left == l
      ensures key == k
      ensures value == v
      ensures isThreadRight == rt
      ensures right == r
      ensures color == c
    {
      key := k;
      value := v;
      isThreadLeft := lt;
      left := l;
      isThreadRight := rt;
      right := r;
      color := c;
    }
  }

  predicate ValidRecP(node: TTNode?, sk: ttreePointer<TTNode>, isThread: bool)
    decreases sk
    reads set x | x in elemsP(sk) :: x`left
    reads set x | x in elemsP(sk) :: x`isThreadLeft
    reads set x | x in elemsP(sk) :: x`right
    reads set x | x in elemsP(sk) :: x`isThreadRight

    ensures sk.Child? ==> ((ValidRecP(node, sk, isThread)) <==> !isThread && ValidRec(node, sk.child))
  {
    match sk {
      case Child(t) => !isThread && ValidRec(node, t)
      case Thread(_) => isThread
    }
  }

  predicate ValidRec(node: TTNode?, sk: ttree<TTNode>)
    decreases sk
    reads set x | x in elems(sk) :: x`left
    reads set x | x in elems(sk) :: x`isThreadLeft
    reads set x | x in elems(sk) :: x`right
    reads set x | x in elems(sk) :: x`isThreadRight
  {
    match sk {
      case Empty => node == null
      case Node(l, x, r) =>
        && x == node
        && x !in elemsP(l)
        && x !in elemsP(r)
        && elemsP(l) !! elemsP(r)
        && ValidRecP(node.left, l, node.isThreadLeft)
        && ValidRecP(node.right, r, node.isThreadRight)
    }
  }

  function TreeModelRecP(sk: ttreePointer<TTNode>): pointer
    reads elemsP(sk)
    ensures sk.Child? ==> (TreeModelRecP(sk) == RB.Child(TreeModelRec(sk.child)))
    ensures (set n | n in elemsP(sk) :: n.key) == pointerKeys(TreeModelRecP(sk))
  {
    match sk {
      case Child(t) => RB.Child(TreeModelRec(t))
      case Thread(n) => RB.Thread(n.key)
    }
  }

  function TreeModelRec(sk: ttree<TTNode>): rbtree
    reads elems(sk)
    ensures (set n | n in elems(sk) :: n.key) == keys(TreeModelRec(sk))
  {
    match sk {
      case Empty => RB.Empty
      case Node(l, n, r) => RB.Node(TreeModelRecP(l), n.key, n.value, TreeModelRecP(r), n.color)
    }
  }


/*
  lemma TreeModelRecChildren(sk: ttree<TTNode>)
    requires sk.Node?
    ensures TreeModelRec(sk).left == TreeModelRec(sk.left)
    ensures TreeModelRec(sk).right == TreeModelRec(sk.right)
  {}
  */

  predicate SearchTreeRec(sk: ttree<TTNode>)
    reads elems(sk)
  {
    RB.SearchTree(TreeModelRec(sk))
  }

  function method isRed(node: TTNode?): bool
    reads node
  {
    node != null && node.color.Red?
  }

  function method isRedLeft(node: TTNode?): bool
    reads node, node.left
    requires node != null
  {
    node.left != null && !node.isThreadLeft && node.left.color.Red?
  }

  function method isRedRight(node: TTNode?): bool
    reads node, node.right
    requires node != null
  {
    node.right != null && !node.isThreadRight && node.right.color.Red?
  }

  lemma isRedProp(node: TTNode?, sk: ttree<TTNode>)
    requires ValidRec(node, sk)
    ensures isRed(node) <==> RB.isRed(TreeModelRec(sk))
  {}

  lemma isRedLeftProp(node: TTNode?, sk: ttree<TTNode>)
    requires ValidRec(node, sk)
    requires node != null
    ensures isRedLeft(node) <==> RB.isRedP(TreeModelRec(sk).left)
  {}

  lemma isRedPropAll(nodes: set<TTNode?>, sks: set<ttree<TTNode>>)
    ensures
      forall node, sk | node in nodes && sk in sks && ValidRec(node, sk)
        :: isRed(node) <==> RB.isRed(TreeModelRec(sk))
  {}

  function method isBlack(node: TTNode?): bool
    reads node
  {
    node != null && node.color.Black?
  }

  lemma isBlackProp(node: TTNode?, sk: ttree<TTNode>)
    requires ValidRec(node, sk)
    ensures isBlack(node) <==> RB.isBlack(TreeModelRec(sk))
  {}

  function BlackHeight(sk: ttree<TTNode>): nat
    reads elems(sk)
  {
    RB.BlackHeight(TreeModelRec(sk))
  }

  predicate RedBlackTreeRec(sk: ttree<TTNode>)
    reads elems(sk)
  {
    RB.RedBlackTree(TreeModelRec(sk))
  }
}
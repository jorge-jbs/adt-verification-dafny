include "../../../src/tree/layer4/TRBTree2/Base.dfy"
include "../../../src/tree/layer4/Tree.dfy"
include "../../../src/tree/KeyValue.dfy"
include "../../../src/tree/layer4/Color.dfy"

module TTNode {
  import opened KeyValue
  import opened RB = TRBTree.Base
  import opened T = Tree
  import opened Color

  class TTNode {
    var key: K;
    var value: V;

    var isThreadLeft: bool
    var left: TTNode?;

    var isThreadRight: bool
    var right: TTNode?;
   
    var color: Color;

    constructor(lt: bool, l: TTNode?, k: K, v: V, rt: bool, r: TTNode?, c: Color)
      ensures left == l
      ensures key == k
      ensures value == v
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

  predicate ValidRec(node: TTNode?, sk: tree<TTNode>)
    reads set x | x in elems(sk) :: x`left
    reads set x | x in elems(sk) :: x`right
  {
    match sk {
      case Empty => node == null
      case Node(l, x, r) =>
        && x == node
        && x !in elems(l)
        && x !in elems(r)
        && elems(l) !! elems(r)
        && ValidRec(node.left, l)
        && ValidRec(node.right, r)
    }
  }

  /*
  predicate ValidRec(node: TTNode?, sk: tree<TTNode>)
    reads set x | x in elems(sk) :: x`left
    reads set x | x in elems(sk) :: x`right
    reads set x | x in elems(sk) :: x`isThreadLeft
    reads set x | x in elems(sk) :: x`isThreadRight
  {
    match sk {
      case Empty => node == null
      case Node(l, x, r) =>
        && x == node
        && x !in elems(l)
        && x !in elems(r)
        && elems(l) !! elems(r)
        && (
          if node.isThreadLeft then
            node.left != null
          else
            ValidRec(node.left, l)
        )
        && (
          if node.isThreadRight then
            node.right != null
          else
            ValidRec(node.right, l)
        )
    }
  }
  */

  function TreeModelRec(sk: tree<TTNode>): rbtree
    reads elems(sk)
    reads set n | n in elems(sk) && n.left != null :: n.left`key
    reads set n | n in elems(sk) && n.right != null :: n.right`key
    //ensures (set n | n in elems(sk) :: n.key) == keys(TreeModelRec(sk))
  {
    match sk {
      case Empty => RB.Empty
      case Node(l, n, r) =>
        RB.Node(
          if n.isThreadLeft && n.left != null then
            Thread(n.left.key)
          else
            TreeModelRec(l),
          n.key,
          n.value,
          if n.isThreadRight && n.right != null then
            Thread(n.right.key)
          else
            TreeModelRec(r),
          n.color
        )
    }
  }

/*
  lemma TreeModelRecChildren(sk: ttree<TTNode>)
    requires sk.Node?
    ensures TreeModelRec(sk).left == TreeModelRec(sk.left)
    ensures TreeModelRec(sk).right == TreeModelRec(sk.right)
  {}
  */

/*
  predicate SearchTreeRec(sk: tree<TTNode>)
    reads elemsAndThreads(sk)
  {
    RB.SearchTree(TreeModelRec(sk))
  }

  function method isRed(node: TTNode?): bool
    reads node
  {
    node != null && node.color.Red?
  }

  lemma isRedProp(node: TTNode?, sk: tree<TTNode>)
    requires ValidRec(node, sk, false)
    ensures isRed(node) <==> RB.isRed(TreeModelRec(sk))
  {}

  lemma isRedPropAll(nodes: set<TTNode?>, sks: set<tree<TTNode>>)
    ensures
      forall node, sk | node in nodes && sk in sks && ValidRec(node, sk, false)
        :: isRed(node) <==> RB.isRed(TreeModelRec(sk))
  {}

  function method isBlack(node: TTNode?): bool
    reads node
  {
    node != null && node.color.Black?
  }

  lemma isBlackProp(node: TTNode?, sk: ttree<TTNode>)
    requires ValidRec(node, sk, false)
    ensures isBlack(node) <==> RB.isBlack(TreeModelRec(sk))
  {}

  function BlackHeight(sk: ttree<TTNode>): nat
    reads elemsAndThreads(sk)
  {
    RB.BlackHeight(TreeModelRec(sk))
  }

  predicate RedBlackTreeRec(sk: ttree<TTNode>)
    reads elemsAndThreads(sk)
  {
    RB.RedBlackTree(TreeModelRec(sk))
  }
  */
}
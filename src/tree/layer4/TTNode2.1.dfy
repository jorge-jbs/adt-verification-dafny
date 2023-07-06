include "../../../src/tree/layer4/TRBTree2/Base.dfy"
include "../../../src/tree/layer4/TTree2.dfy"
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

  predicate ValidRec(node: TTNode?, sk: ttree<TTNode>, isThread: bool)
    reads set x | x in elems(sk) :: x`left
    reads set x | x in elems(sk) :: x`isThreadLeft
    reads set x | x in elems(sk) :: x`right
    reads set x | x in elems(sk) :: x`isThreadRight
  {
    match sk {
      case Empty => !isThread && node == null
      case Thread(_) => isThread
      case Node(l, x, r) =>
        && !isThread
        && x == node
        && x !in elems(l)
        && x !in elems(r)
        && elems(l) !! elems(r)
        && ValidRec(node.left, l, node.isThreadLeft)
        && ValidRec(node.right, r, node.isThreadRight)
    }
  }

  function TreeModelRec(sk: ttree<TTNode>): rbtree
    //reads elemsAndThreads(sk)
    reads set x | x in subtrees(sk) && x.Thread? :: x.thread`key
    reads set x | x in subtrees(sk) && x.Node? :: x.data`left
    reads set x | x in subtrees(sk) && x.Node? :: x.data`key
    reads set x | x in subtrees(sk) && x.Node? :: x.data`value
    reads set x | x in subtrees(sk) && x.Node? :: x.data`color
    ensures (set n | n in elems(sk) :: n.key) == keys(TreeModelRec(sk))
  {
    match sk {
      case Empty => RB.Empty
      case Thread(n) => RB.Thread(n.key)
      case Node(l, n, r) =>
        RB.Node(
          TreeModelRec(l),
          n.key,
          n.value,
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

  predicate SearchTreeRec(sk: ttree<TTNode>)
    reads elemsAndThreads(sk)
  {
    RB.SearchTree(TreeModelRec(sk))
  }

  function method isRed(node: TTNode?): bool
    reads node
  {
    node != null && node.color.Red?
  }

  lemma isRedProp(node: TTNode?, sk: ttree<TTNode>)
    requires ValidRec(node, sk, false)
    ensures isRed(node) <==> RB.isRed(TreeModelRec(sk))
  {}

  lemma isRedPropAll(nodes: set<TTNode?>, sks: set<ttree<TTNode>>)
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
}
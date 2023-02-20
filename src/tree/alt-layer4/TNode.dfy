include "../../../src/tree/alt-layer4/RBTree.dfy"
include "../../../src/tree/alt-layer4/Tree.dfy"
include "../../../src/tree/alt-layer4/KeyValue.dfy"
include "../../../src/tree/alt-layer4/Color.dfy"

module TNode {
  import opened KeyValue
  import opened RB = RBTree
  import opened T = Tree
  import opened Color

  class TNode {
    var key: K;
    var value: V;
    var left: TNode?;
    var right: TNode?;
    var color: Color;

    constructor(l: TNode?, k: K, v: V, r: TNode?)
      ensures left == l
      ensures key == k
      ensures value == v
      ensures right == r
      ensures color == Black
    {
      key := k;
      value := v;
      left := l;
      right := r;
      color := Black;
    }

    constructor RedBlack(l: TNode?, k: K, v: V, r: TNode?, c: Color)
      ensures left == l
      ensures key == k
      ensures value == v
      ensures right == r
      ensures color == c
    {
      key := k;
      value := v;
      left := l;
      right := r;
      color := c;
    }

    constructor Leaf(k: K, v: V)
      ensures left == null
      ensures key == k
      ensures value == v
      ensures right == null
    {
      key := k;
      value := v;
      left := null;
      right := null;
      color := Black;
    }
  }

  predicate ValidRec(node: TNode?, sk: tree<TNode>)
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

  function TreeModelRec(sk: tree<TNode>): rbtree
    reads elems(sk)
    ensures (set n | n in elems(sk) :: n.key) == keys(TreeModelRec(sk))
  {
    match sk {
      case Empty => RB.Empty
      case Node(l, n, r) => RB.Node(TreeModelRec(l), n.key, n.value, TreeModelRec(r), n.color)
    }
  }

  predicate SearchTreeRec(sk: tree<TNode>)
    reads elems(sk)
  {
    RB.SearchTree(TreeModelRec(sk))
  }

  function method isRed(node: TNode?): bool
    reads node
  {
    node != null && node.color.Red?
  }

  lemma isRedProp(node: TNode?, sk: tree<TNode>)
    requires ValidRec(node, sk)
    ensures isRed(node) <==> RB.isRed(TreeModelRec(sk))
  {}

  function method isBlack(node: TNode?): bool
    reads node
  {
    node != null && node.color.Black?
  }

  function BlackHeight(sk: tree<TNode>): nat
    reads elems(sk)
  {
    RB.BlackHeight(TreeModelRec(sk))
  }

  predicate RedBlackTreeRec(sk: tree<TNode>)
    reads elems(sk)
  {
    RB.RedBlackTree(TreeModelRec(sk))
  }
}
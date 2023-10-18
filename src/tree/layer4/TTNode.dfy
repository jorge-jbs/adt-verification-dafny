include "../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../src/tree/layer4/TTree.dfy"
include "../../../src/tree/KeyValue.dfy"
include "../../../src/tree/layer4/Color.dfy"

module TTNode {
  import opened KeyValue
  import opened TRB = TRBTree.Base
  import opened T = TTree
  import opened Color

  class TTNode {
    const key: K
    var value: V

    var isThreadLeft: bool
    var left: TTNode?

    var isThreadRight: bool
    var right: TTNode?

    var color: Color

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

  predicate ValidChild(node: TTNode?, sk: ttreeOrThread<TTNode>, isThread: bool)
    decreases sk, 1
    reads set x | x in elems(sk) :: x`left
    reads set x | x in elems(sk) :: x`isThreadLeft
    reads set x | x in elems(sk) :: x`right
    reads set x | x in elems(sk) :: x`isThreadRight
  {
    match sk {
      case Thread(n) => isThread && node == n
      case _ => !isThread && ValidRec(node, sk)
    }
  }

  predicate ValidRec'(node: TTNode?, sk: ttree<TTNode>)
    decreases sk, 0
    reads set x | x in elems(sk) :: x`left
    reads set x | x in elems(sk) :: x`isThreadLeft
    reads set x | x in elems(sk) :: x`right
    reads set x | x in elems(sk) :: x`isThreadRight
    //ensures ValidRec(node, sk, parents) <==> ValidRec'(node, sk, parents)
  {
    match sk {
      case Empty => node == null
      case Node(l, x, r) =>
        && x == node
        && x !in elems(l)
        && x !in elems(r)
        && elems(l) !! elems(r)
        && ValidChild(node.left, l, node.isThreadLeft)
        && ValidChild(node.right, r, node.isThreadRight)
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
        && x !in elems(l)
        && x !in elems(r)
        && elems(l) !! elems(r)

        //&& ValidChild(node.left, l, node.isThreadLeft)
        && (
          if l.Thread? then
            node.isThreadLeft && node.left == l.thread
          else
            !node.isThreadLeft && ValidRec(node.left, sk.left)
        )

        //&& ValidChild(node.right, r, node.isThreadRight)
        && (
          if r.Thread? then
            node.isThreadRight && node.right == r.thread
          else
            !node.isThreadRight && ValidRec(node.right, sk.right)
        )
    }
  }

  function nodeToThread(node: TTNode?): T.threadOrEmpty<TTNode>
  {
    if node == null then
      T.Empty
    else
      T.Thread(node as TTNode)
  }

  ghost function GetSk(
      node: TTNode,
      root: TTNode,
      rootSk: ttree<TTNode>
    ): ttree<TTNode>
    reads elems(rootSk)

    requires ValidRec(root, rootSk)
    requires node in elems(rootSk)
    requires SearchTree(TreeModelRec(rootSk))

    ensures ValidRec(node, GetSk(node, root, rootSk))
    ensures node.key in keys(TreeModelRec(rootSk))
    ensures TreeModelRec(GetSk(node, root, rootSk))
      == GetSubtree(TreeModelRec(rootSk), node.key)
  {
    if node in elems(rootSk.left) then
      assert ValidRec(root.left, rootSk.left);
      GetSk(node, root.left, rootSk.left)
    else if node in elems(rootSk.right) then
      assert ValidRec(root.right, rootSk.right);
      GetSk(node, root.right, rootSk.right)
    else
      rootSk
  }

  /*
  ghost function GetSk(
      node: TTNode,
      root: TTNode,
      prev: T.threadOrEmpty<TTNode>,
      rootSk: ttree<TTNode>,
      next: T.threadOrEmpty<TTNode>
    ): ttree<TTNode>
    reads elems(rootSk)
    requires ValidRec(root, rootSk)
    //requires rootSk.Node? ==> ThreadedNe(prev, rootSk, next)
    requires node in elems(rootSk)
    requires SearchTree(TreeModelRec(rootSk))
    ensures ValidRec(node, GetSk(node, root, prev, rootSk, next))
    //ensures ThreadedNe(prev, GetSk(node, root, prev, rootSk, next), next)
    ensures node.key in keys(TreeModelRec(rootSk))
    ensures TreeModelRec(GetSk(node, root, prev, rootSk, next))
      == GetSubtree(TreeModelRec(rootSk), node.key)
  {
    if node in elems(rootSk.left) then
      assert ValidRec(root.left, rootSk.left);
      GetSk(node, root.left, prev, rootSk.left, T.Thread(rootSk.data))
    else if node in elems(rootSk.right) then
      assert ValidRec(root.right, rootSk.right);
      GetSk(node, root.right, T.Thread(rootSk.data), rootSk.right, next)
    else
      rootSk
  }
  */

  lemma EqOfValid(node: TTNode?, sk: ttree<TTNode>, sk': ttree<TTNode>)
    requires ValidRec(node, sk)
    requires ValidRec(node, sk')
    ensures sk == sk'
  {
    if node == null {
    } else {
      if !sk.left.Thread? {
        EqOfValid(node.left, sk.left, sk'.left);
      }
      if !sk.right.Thread? {
        EqOfValid(node.right, sk.right, sk'.right);
      }
    }
  }

  lemma SubtreeOfInElemsRoot(
      node: TTNode?,
      sk: ttree<TTNode>,
      root: TTNode?,
      rootSk: ttree<TTNode>
    )
    requires ValidRec(node, sk)
    requires ValidRec(root, rootSk)
    requires node in elems(rootSk)
    ensures T.Subtree(sk, rootSk)
    ensures elemsAndThreads(sk) <= elemsAndThreads(rootSk)
  {
    if node == root {
      EqOfValid(node, sk, rootSk);
    } else {
      if !rootSk.left.Thread? && node in elems(rootSk.left) {
        SubtreeOfInElemsRoot(node, sk, root.left, rootSk.left);
      }
      if !rootSk.right.Thread? && node in elems(rootSk.right) {
        SubtreeOfInElemsRoot(node, sk, root.right, rootSk.right);
      }
    }
  }

  function TreeModelRec(sk: ttreeOrThread<TTNode>): trbtreeOrThread
    reads elems(sk)
  {
    match sk {
      case Empty => TRB.Empty
      case Thread(n) => TRB.Thread(n.key)
      case Node(l, n, r) => TRB.Node(TreeModelRec(l), n.key, n.value, TreeModelRec(r), n.color)
    }
  }

  predicate SearchTreeRec(sk: ttree<TTNode>)
    reads elems(sk)
  {
    TRB.SearchTree(TreeModelRec(sk))
  }

  function isRed(node: TTNode?): bool
    reads node
  {
    node != null && node.color.Red?
  }

  function isRedLeft(node: TTNode?): bool
    reads node, node.left
    requires node != null
  {
    node.left != null && !node.isThreadLeft && node.left.color.Red?
  }

  lemma isRedLeftProp(node: TTNode?, sk: ttree<TTNode>)
    requires ValidRec(node, sk)
    requires node != null
    ensures isRedLeft(node) <==> TRB.isRed(TreeModelRec(sk).left)
  {}

  function isRedRight(node: TTNode?): bool
    reads node, node.right
    requires node != null
  {
    node.right != null && !node.isThreadRight && node.right.color.Red?
  }

  lemma isRedProp(node: TTNode?, sk: ttree<TTNode>)
    requires ValidRec(node, sk)
    ensures isRed(node) <==> TRB.isRed(TreeModelRec(sk))
  {}

  lemma isRedPropAll(nodes: set<TTNode?>, sks: set<ttree<TTNode>>)
    ensures
      forall node, sk | node in nodes && sk in sks && ValidRec(node, sk)
        :: isRed(node) <==> TRB.isRed(TreeModelRec(sk))
  {}

  function isBlack(node: TTNode?): bool
    reads node
  {
    node != null && node.color.Black?
  }

  lemma isBlackProp(node: TTNode?, sk: ttree<TTNode>)
    requires ValidRec(node, sk)
    ensures isBlack(node) <==> TRB.isBlack(TreeModelRec(sk))
  {}

  function isBlackLeft(node: TTNode?): bool
    reads node, node.left
    requires node != null
  {
    node.left != null && !node.isThreadLeft && node.left.color.Black?
  }

  lemma isBlackLeftProp(node: TTNode?, sk: ttree<TTNode>)
    requires ValidRec(node, sk)
    requires node != null
    ensures isBlackLeft(node) <==> TRB.isBlack(TreeModelRec(sk).left)
  {}

  function isBlackRight(node: TTNode?): bool
    reads node, node.right
    requires node != null
  {
    node.right != null && !node.isThreadRight && node.right.color.Black?
  }

  lemma isBlackRightProp(node: TTNode?, sk: ttree<TTNode>)
    requires ValidRec(node, sk)
    requires node != null
    ensures isBlackRight(node) <==> TRB.isBlack(TreeModelRec(sk).right)
  {}

  function BlackHeight(sk: ttree<TTNode>): nat
    reads elems(sk)
  {
    TRB.BlackHeight(TreeModelRec(sk))
  }

  predicate RedBlackTreeRec(sk: ttree<TTNode>)
    reads elems(sk)
  {
    TRB.RedBlackTree(TreeModelRec(sk))
  }
}
include "../../../../src/Collections/KeyValue.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTree.dfy"

module ThreadedLinkedTree.Impl.TTNode {
  import opened KeyValue
  import opened TRB = Model.Base
  import opened T = TTree
  import opened Model.Color

  /*
  A threaded red-black tree node.

  The key cannot be changed (if you want to update a node, create a new
  one and replace it). Making the key immutable helps verifying iterators.

  `left` (resp. `right`) is a link to the left (resp. right) child if
  `isThreadLeft` (resp. `isThreadRight`) is set to false. Otherwise,
  `left` (resp. `right`) holds a link to the previous (resp. next) node
  in the inorder traversal of the tree, and the left (resp. right) child
  is assumed to be empty. If `left` (resp. `right`) is set to null in
  some node, that node is the leftmost (resp. rightmost) node of the tree.

  The skeleton of a tree is represented with a ttree. That tree can be
  transformed to the model via the TreeModelRec.

  Red-black tree invariants are not specified on linked nodes, but on
  the functional model.
  */
  class TTNode {
    const key: K
    var value: V
    var color: Color

    var isThreadLeft: bool
    var left: TTNode?

    var isThreadRight: bool
    var right: TTNode?

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

  lemma {:induction t} KeysAndElems(t: ttree<TTNode>)
    ensures TRB.keys(TreeModelRec(t)) == set n | n in elems(t) :: n.key
  {}

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
    ensures elems(GetSk(node, root, rootSk)) <= elems(rootSk)
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

  lemma GetValue(
      node: TTNode,
      root: TTNode,
      rootSk: ttree<TTNode>
    )
    requires ValidRec(root, rootSk)
    requires SearchTree(TreeModelRec(rootSk))
    requires node in elems(rootSk)
    requires assert node.key in keys(TreeModelRec(rootSk)) by { KeysAndElems(rootSk); } true
    ensures node.value == Get'(TreeModelRec(rootSk), node.key)
  {
    if node == root {
    } else if node in elems(rootSk.left) {
      assert node.key in keys(TreeModelRec(rootSk).left) by {
        KeysAndElems(rootSk.left);
      }
      GetValue(node, root.left, rootSk.left);
    } else {
      assert node.key in keys(TreeModelRec(rootSk).right) by {
        KeysAndElems(rootSk.right);
      }
      GetValue(node, root.right, rootSk.right);
    }
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

  lemma ThreadedRecLImp(prev: T.threadOrEmpty<TTNode>, t: ttreeOrThread<TTNode>, next: T.threadOrEmpty<TTNode>)
    decreases t
    ensures ThreadedRecL(prev, t, next) ==>
      TRB.ThreadedTreeRecL(TreeModelRec(prev), TreeModelRec(t), TreeModelRec(next))
  {
    if t.Node? {
      ThreadedRecLImp(prev, t.left, T.Thread(t.data));
      ThreadedRecRImp(T.Thread(t.data), t.right, next);
    }
  }

  lemma ThreadedRecRImp(prev: T.threadOrEmpty<TTNode>, t: ttreeOrThread<TTNode>, next: T.threadOrEmpty<TTNode>)
    decreases t
    ensures ThreadedRecR(prev, t, next) ==>
      TRB.ThreadedTreeRecR(TreeModelRec(prev), TreeModelRec(t), TreeModelRec(next))
  {
    if t.Node? {
      ThreadedRecLImp(prev, t.left, T.Thread(t.data));
      ThreadedRecRImp(T.Thread(t.data), t.right, next);
    }
  }

  lemma ThreadedNeImp(prev: T.threadOrEmpty<TTNode>, t: nettree<TTNode>, next: T.threadOrEmpty<TTNode>)
    decreases t
    ensures ThreadedNe(prev, t, next) ==>
      TRB.ThreadedTreeNe(TreeModelRec(prev), TreeModelRec(t), TreeModelRec(next))
  {
    ThreadedRecLImp(prev, t.left, T.Thread(t.data));
    ThreadedRecRImp(T.Thread(t.data), t.right, next);
  }

  lemma ThreadedRootImp(t: ttree<TTNode>)
    ensures ThreadedRoot(t) ==> TRB.ThreadedTreeRoot(TreeModelRec(t))
  {
    if t.Node? {
      ThreadedNeImp(T.Empty, t, T.Empty);
    }
  }

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

  lemma isRedRightProp(node: TTNode?, sk: ttree<TTNode>)
    requires ValidRec(node, sk)
    requires node != null
    ensures isRedRight(node) <==> TRB.isRed(TreeModelRec(sk).right)
  {}

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
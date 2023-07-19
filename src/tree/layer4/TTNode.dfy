include "../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../src/tree/layer4/TTree.dfy"
include "../../../src/tree/KeyValue.dfy"
include "../../../src/tree/layer4/Color.dfy"

module TTNode {
  import opened KeyValue
  import opened RB = TRBTree.Base
  import opened T = TTree
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

    ensures sk.Child? ==> (ValidRecP(node, sk, isThread) <==> !isThread && ValidRec(node, sk.child))
  {
    match sk {
      case Child(t) => !isThread && ValidRec(node, t)
      case Thread(n) => isThread && node == n
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

  function method nodeToPointer(node: TTNode?): RB.threadOrEmpty
  {
    if node == null then
      RB.Child(RB.Empty)
    else
      RB.Thread(node.key)
  }

  predicate ThreadedRecPL(prev: TTNode?, node: TTNode?, sk: ttreePointer<TTNode>, next: TTNode?)
    decreases sk
    reads set x | x in elemsP(sk) :: x`left
    reads set x | x in elemsP(sk) :: x`isThreadLeft
    reads set x | x in elemsP(sk) :: x`right
    reads set x | x in elemsP(sk) :: x`isThreadRight

    requires ValidRecP(node, sk, true) || ValidRecP(node, sk, false)
    ensures ThreadedRecPL(prev, node, sk, next) ==> RB.ThreadedTreeRecPL(nodeToPointer(prev), TreeModelRecP(sk), nodeToPointer(next))
    ensures sk.Child? && sk.child.Node? ==>
      (ThreadedRecPL(prev, node, sk, next) <==> ThreadedRec(prev, node, sk.child, next))
  {
    match sk {
      case Child(Empty) => prev == null
      case Child(t) => ThreadedRec(prev, node, t, next)
      case Thread(n) => prev == n
    }
  }

  predicate ThreadedRecPR(prev: TTNode?, node: TTNode?, sk: ttreePointer<TTNode>, next: TTNode?)
    decreases sk
    reads set x | x in elemsP(sk) :: x`left
    reads set x | x in elemsP(sk) :: x`isThreadLeft
    reads set x | x in elemsP(sk) :: x`right
    reads set x | x in elemsP(sk) :: x`isThreadRight

    requires ValidRecP(node, sk, true) || ValidRecP(node, sk, false)
    ensures ThreadedRecPR(prev, node, sk, next) ==>
      RB.ThreadedTreeRecPR(nodeToPointer(prev), TreeModelRecP(sk), nodeToPointer(next))
    ensures sk.Child? && sk.child.Node? ==>
      (ThreadedRecPR(prev, node, sk, next) <==> ThreadedRec(prev, node, sk.child, next))
  {
    match sk {
      case Child(Empty) => next == null
      case Child(t) => ThreadedRec(prev, node, t, next)
      case Thread(n) => next == n
    }
  }

  predicate ThreadedRec(prev: TTNode?, node: TTNode?, sk: ttree<TTNode>, next: TTNode?)
    decreases sk
    reads set x | x in elems(sk) :: x`left
    reads set x | x in elems(sk) :: x`isThreadLeft
    reads set x | x in elems(sk) :: x`right
    reads set x | x in elems(sk) :: x`isThreadRight

    requires ValidRec(node, sk)
    requires node != null
    ensures ThreadedRec(prev, node, sk, next) ==>
      RB.ThreadedTreeRec(nodeToPointer(prev), TreeModelRec(sk), nodeToPointer(next))
  {
    match sk {
      case Node(l, x, r) =>
        && ThreadedRecPL(prev, node.left, l, node)
        && ThreadedRecPR(node, node.right, r, next)
    }
  }

  predicate ThreadedRoot(node: TTNode?, sk: ttree<TTNode>)
    decreases sk
    reads set x | x in elems(sk) :: x`left
    reads set x | x in elems(sk) :: x`isThreadLeft
    reads set x | x in elems(sk) :: x`right
    reads set x | x in elems(sk) :: x`isThreadRight

    requires ValidRec(node, sk)
  {
    match sk {
      case Empty => true
      case Node(_, _, _) => ThreadedRec(null, node, sk, null)
    }
  }

  lemma ElemsOfThreadRecP(prev: TTNode?, node: TTNode?, sk: ttreePointer<TTNode>, next: TTNode?, visited: set<TTNode>)
      returns (threads: set<TTNode>)
    decreases sk
    requires ValidRecP(node, sk, true) || ValidRecP(node, sk, false)
    requires prev != null ==> prev in visited
    requires next != null ==> next in visited
    requires ThreadedRecPL(prev, node, sk, next) || ThreadedRecPR(prev, node, sk, next)
    ensures elemsAndThreadsP(sk) <= elemsP(sk) + visited
    ensures threads <= visited
    ensures elemsAndThreadsP(sk) == elemsP(sk) + threads
  {
    match sk {
      case Child(Empty) => {
        threads := {};
      }
      case Child(_) => {
        threads := ElemsOfThreadRec(prev, node, sk.child, next, visited);
      }
      case Thread(n) => {
        assert n == next || n == prev;
        threads := {n};
      }
    }
  }

  lemma ElemsOfThreadRec(prev: TTNode?, node: TTNode?, sk: ttree<TTNode>, next: TTNode?, visited: set<TTNode>)
      returns (threads: set<TTNode>)
    decreases sk
    requires ValidRec(node, sk)
    requires node != null
    requires prev != null ==> prev in visited
    requires next != null ==> next in visited
    requires ThreadedRec(prev, node, sk, next)
    ensures elemsAndThreads(sk) <= elems(sk) + visited
    ensures threads <= visited
    ensures elemsAndThreads(sk) == elems(sk) + threads
  {
    match sk {
      case Node(l, x, r) => {
        var threadsL := ElemsOfThreadRecP(prev, node.left, sk.left, node, visited + {node});
        var threadsR := ElemsOfThreadRecP(node, node.right, sk.right, next, visited + {node});
        threads := threadsL + threadsR - {node};
      }
    }
  }

  lemma ElemsOfThreadRoot(node: TTNode?, sk: ttree<TTNode>)
    requires ValidRec(node, sk)
    requires ThreadedRoot(node, sk)
    ensures elems(sk) == elemsAndThreads(sk)
  {
    if node != null {
      var _ := ElemsOfThreadRec(null, node, sk, null, {});
    }
  }

  function GetSk(node: TTNode, root: TTNode?, rootSk: ttree<TTNode>): ttree<TTNode>
    reads elems(rootSk)
    requires ValidRec(root, rootSk)
    requires node in elems(rootSk)
    requires SearchTree(TreeModelRec(rootSk))
    ensures ValidRec(node, GetSk(node, root, rootSk))
    ensures node.key in keys(TreeModelRec(rootSk))
    ensures TreeModelRec(GetSk(node, root, rootSk)) == GetSubtree(TreeModelRec(rootSk), node.key)
  {
    if node in elemsP(rootSk.left) then
      GetSk(node, root.left, rootSk.left.child)
    else if node in elemsP(rootSk.right) then
      GetSk(node, root.right, rootSk.right.child)
    else
      rootSk
  }


  lemma EqOfValid(node: TTNode?, sk: ttree<TTNode>, sk': ttree<TTNode>)
    requires ValidRec(node, sk)
    requires ValidRec(node, sk')
    ensures sk == sk'
  {
    if node == null {
    } else {
      if sk.left.Child? {
        EqOfValid(node.left, sk.left.child, sk'.left.child);
      }
      if sk.right.Child? {
        EqOfValid(node.right, sk.right.child, sk'.right.child);
      }
    }
  }

  lemma SubtreeOfInElemsRoot(node: TTNode?, sk: ttree<TTNode>, root: TTNode?, rootSk: ttree<TTNode>)
    requires ValidRec(node, sk)
    requires ValidRec(root, rootSk)
    requires node in elems(rootSk)
    ensures T.Subtree(sk, rootSk)
    ensures elemsAndThreads(sk) <= elemsAndThreads(rootSk)
  {
    if node == root {
      EqOfValid(node, sk, rootSk);
    } else {
      if rootSk.left.Child? && node in elems(rootSk.left.child) {
        SubtreeOfInElemsRoot(node, sk, root.left, rootSk.left.child);
      }
      if rootSk.right.Child? && node in elems(rootSk.right.child) {
        SubtreeOfInElemsRoot(node, sk, root.right, rootSk.right.child);
      }
    }
  }

  function TreeModelRecP(sk: ttreePointer<TTNode>): pointer
    reads elemsP(sk)
    ensures sk.Child? ==> (TreeModelRecP(sk) == RB.Child(TreeModelRec(sk.child)))
    ensures (set n | n in elemsP(sk) :: n.key) == keysP(TreeModelRecP(sk))
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
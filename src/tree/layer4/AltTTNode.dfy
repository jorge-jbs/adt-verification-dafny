include "../../../src/tree/layer4/AltTRBTree/Base.dfy"
include "../../../src/tree/layer4/AltTTree.dfy"
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

  predicate ValidChild(node: TTNode?, sk: ttreeOrThread<TTNode>, isThread: bool, parents: set<TTNode>)
    decreases sk, 1
    reads set x | x in elems(sk) :: x`left
    reads set x | x in elems(sk) :: x`isThreadLeft
    reads set x | x in elems(sk) :: x`right
    reads set x | x in elems(sk) :: x`isThreadRight
  {
    match sk {
      case Thread(n) => isThread && node == n && node in parents
      case _ => !isThread && ValidRec(node, sk, parents)
    }
  }

  predicate ValidRec'(node: TTNode?, sk: ttree<TTNode>, parents: set<TTNode>)
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
        && ValidChild(node.left, l, node.isThreadLeft, parents + {node})
        && ValidChild(node.right, r, node.isThreadRight, parents + {node})
    }
  }

  predicate ValidRec(node: TTNode?, sk: ttree<TTNode>, parents: set<TTNode>)
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
        //&& ValidChild(node.left, l, node.isThreadLeft, parents + {node})
        //&& ValidChild(node.right, r, node.isThreadRight, parents + {node})
        && (
          if l.Thread? then
            node.isThreadLeft && node.left == l.thread && node.left in parents
          else
            !node.isThreadLeft && ValidRec(node.left, sk.left, parents + {node})
        )
        && (
          if r.Thread? then
            node.isThreadRight && node.right == r.thread && node.right in parents
          else
            !node.isThreadRight && ValidRec(node.right, sk.right, parents + {node})
        )
    }
  }

  predicate ValidRoot(node: TTNode?, sk: ttree<TTNode>)
    decreases sk, 0
    reads set x | x in elems(sk) :: x`left
    reads set x | x in elems(sk) :: x`isThreadLeft
    reads set x | x in elems(sk) :: x`right
    reads set x | x in elems(sk) :: x`isThreadRight
  {
    ValidRec(node, sk, {})
  }

  function nodeToThreadOrEmpty(node: TTNode?): TRB.threadOrEmpty
  {
    if node == null then
      TRB.Empty
    else
      TRB.Thread(node.key)
  }

  lemma ElemsAndThreadsRec(node: TTNode?, sk: ttree<TTNode>, parents: set<TTNode>)
      returns (threads: set<TTNode>)
    requires ValidRec(node, sk, parents)
    ensures elemsAndThreads(sk) <= elems(sk) + parents
    ensures threads <= parents
    ensures elemsAndThreads(sk) == elems(sk) + threads 
  {
    if sk.Node? {
      var threadsL;
      if !sk.left.Thread? {
        threadsL := ElemsAndThreadsRec(node.left, sk.left, parents + {node});
      } else {
        threadsL := {node.left};
      }
      var threadsR;
      if !sk.right.Thread? {
        threadsR := ElemsAndThreadsRec(node.right, sk.right, parents + {node});
      } else {
        threadsR := {node.right};
      }
      return threadsL + threadsR - {node};
    } else {
      return {};
    }
  }

  lemma ElemsAndThreads(node: TTNode?, sk: ttree<TTNode>)
    requires ValidRoot(node, sk)
    ensures elems(sk) == elemsAndThreads(sk)
  {
    var _ := ElemsAndThreadsRec(node, sk, {});
  }

  function GetSk(
      node: TTNode, 
      root: TTNode?, 
      rootSk: ttree<TTNode>, 
      rootParents: set<TTNode>): (ttree<TTNode>, set<TTNode>)
    reads elems(rootSk)
    requires ValidRec(root, rootSk, rootParents)
    requires node in elems(rootSk)
    requires SearchTree(TreeModelRec(rootSk))
    ensures ValidRec(
      node,
      GetSk(node, root, rootSk, rootParents).0,
      GetSk(node, root, rootSk, rootParents).1
    )
    ensures node.key in keys(TreeModelRec(rootSk))
    ensures TreeModelRec(GetSk(node, root, rootSk, rootParents).0) == GetSubtree(TreeModelRec(rootSk), node.key)
  {
    if node in elems(rootSk.left) then
      GetSk(node, root.left, rootSk.left, rootParents + {root})
    else if node in elems(rootSk.right) then
      GetSk(node, root.right, rootSk.right, rootParents + {root})
    else
      (rootSk, rootParents)
  }

  lemma EqOfValid(
      node: TTNode?, 
      sk: ttree<TTNode>, 
      sk': ttree<TTNode>,
      parents: set<TTNode>,
      parents': set<TTNode>
    )
    requires ValidRec(node, sk, parents)
    requires ValidRec(node, sk', parents')
    ensures sk == sk'
  {
    if node == null {
    } else {
      if !sk.left.Thread? {
        EqOfValid(node.left, sk.left, sk'.left, parents + {node}, parents' + {node});
      }
      if !sk.right.Thread? {
        EqOfValid(node.right, sk.right, sk'.right, parents + {node} , parents' + {node});
      }
    }
  }

  lemma SubValidRec(node: TTNode?, sk: ttree<TTNode>, parents: set<TTNode>, parents': set<TTNode>)
    requires ValidRec(node, sk, parents)
    requires parents <= parents'
    ensures ValidRec(node, sk, parents')
  {}

  lemma SubValidChild(node: TTNode?, sk: ttreeOrThread<TTNode>, isThread: bool, parents: set<TTNode>, parents': set<TTNode>)
    requires ValidChild(node, sk, isThread, parents)
    requires parents <= parents'
    ensures ValidChild(node, sk, isThread, parents')
  {
    match sk
    case Thread(_) =>  {}
    case _ => {
      SubValidRec(node, sk, parents, parents');
    }
  }

  lemma SubtreeOfInElemsRoot(
      node: TTNode?,
      sk: ttree<TTNode>,
      parents: set<TTNode>,
      root: TTNode?,
      rootSk: ttree<TTNode>,
      rootParents: set<TTNode>
    )
    requires ValidRec(node, sk, parents)
    requires ValidRec(root, rootSk, rootParents)
    requires node in elems(rootSk)
    ensures T.Subtree(sk, rootSk)
    ensures elemsAndThreads(sk) <= elemsAndThreads(rootSk)
  {
    if node == root {
      EqOfValid(node, sk, rootSk, parents, rootParents);
    } else {
      if !rootSk.left.Thread? && node in elems(rootSk.left) {
        SubtreeOfInElemsRoot(node, sk, parents, root.left, rootSk.left, rootParents + {root});
      }
      if !rootSk.right.Thread? && node in elems(rootSk.right) {
        SubtreeOfInElemsRoot(node, sk, parents, root.right, rootSk.right, rootParents + {root});
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

  function isRedRight(node: TTNode?): bool
    reads node, node.right
    requires node != null
  {
    node.right != null && !node.isThreadRight && node.right.color.Red?
  }

  lemma isRedProp(node: TTNode?, sk: ttree<TTNode>, parents: set<TTNode>)
    requires ValidRec(node, sk, parents)
    ensures isRed(node) <==> TRB.isRed(TreeModelRec(sk))
  {}

  lemma isRedPropAll(nodes: set<TTNode?>, sks: set<ttree<TTNode>>)
    ensures
      forall node, sk, parents | node in nodes && sk in sks && ValidRec(node, sk, parents)
        :: isRed(node) <==> TRB.isRed(TreeModelRec(sk))
  {}

  function isBlack(node: TTNode?): bool
    reads node
  {
    node != null && node.color.Black?
  }

  lemma isBlackProp(node: TTNode?, sk: ttree<TTNode>, parents: set<TTNode>)
    requires ValidRec(node, sk, parents)
    ensures isBlack(node) <==> TRB.isBlack(TreeModelRec(sk))
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
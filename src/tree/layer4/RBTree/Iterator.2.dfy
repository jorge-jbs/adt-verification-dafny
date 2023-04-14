include "../../../../src/tree/layer4/KeyValue.dfy"
include "../../../../src/tree/layer4/RBTree/Base.dfy"

module RBTree.Iterator {
  import opened KeyValue
  import opened Base

  function DescendAndPush(st: seq<rbtree>, node: rbtree): seq<rbtree>
    decreases node
  {
    if node.Empty? then
      st
    else
      DescendAndPush(st + [node], node.left)
  }

  predicate ValidStack(st: seq<rbtree>)
  {
    forall k | 0 <= k < |st| :: st[k].Node?
  }

  function inorderStack(st: seq<rbtree>): seq<(K, V)>
    requires ValidStack(st)
  {
    if st == [] then
      []
    else
      var node := st[|st|-1];
      if node.Empty? then
        inorderStack(st[..|st|-1])
      else
        [(node.key, node.value)] + inorder(node.right) + inorderStack(st[..|st|-1])
  }

  lemma DescendAndPushSpec(root: rbtree, st: seq<rbtree>, node: rbtree, traversed: seq<(K, V)>)
    decreases node

    requires ValidStack(st)
    requires inorder(root) == traversed + inorder(node) + inorderStack(st)

    ensures ValidStack(DescendAndPush(st, node))
    ensures inorder(root) == traversed + inorderStack(DescendAndPush(st, node))
  {
    if node.Empty? {
    } else {
      DescendAndPushSpec(root, st + [node], node.left, traversed);
    }
  }

  function Next(st: seq<rbtree>): seq<rbtree>
    requires st != []  // has next
    requires ValidStack(st)
  {
    var node := st[|st|-1];
    DescendAndPush(st[..|st|-1], node.right)
  }

  lemma NextSpec(root: rbtree, st: seq<rbtree>, traversed: seq<(K, V)>)
    requires st != []
    requires ValidStack(st)
    requires inorder(root) == traversed + inorderStack(st)

    ensures ValidStack(Next(st))
    ensures inorder(root) == traversed + [(st[|st|-1].key, st[|st|-1].value)] + inorderStack(Next(st))
  {
    var node := st[|st|-1];
    DescendAndPushSpec(root, st[..|st|-1], node.right, traversed + [(node.key, node.value)]);
  }
}
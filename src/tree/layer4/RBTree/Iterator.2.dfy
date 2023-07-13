include "../../../../src/tree/KeyValue.dfy"
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
      [(node.key, node.value)] + inorder(node.right) + inorderStack(st[..|st|-1])
  }

  lemma InorderStackFirst(st: seq<rbtree>)
    requires ValidStack(st)
    requires st != []
    ensures st[|st|-1].key == inorderStack(st)[0].0;
    ensures st[|st|-1].value == inorderStack(st)[0].1;
  {}

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

  function SearchAndPush(st: seq<rbtree>, node: rbtree, k: K): seq<rbtree>
    decreases node
    requires SearchTree(node)
    requires k in keys(node)
  {
    if node.key == k then
      st + [node]
    else if node.key < k then
      SearchAndPush(st, node.right, k)
    else
      SearchAndPush(st + [node], node.left, k)
  }

  lemma Associativity1()
    ensures forall a: seq<(K, V)>, b, c, d, e, f ::
      a + b + (c + d + e) + f == a + b + c + d + e + f
  {}

  lemma Associativity2()
    ensures forall a: seq<(K, V)>, b, c, d ::
      a + b + c + d == a + (b + c + d)
  {}

  lemma SearchAndPushSpec(root: rbtree, st: seq<rbtree>, node: rbtree, k: K)
    decreases node

    requires SearchTree(root)
    requires Subtree(node, root)
    requires k in keys(node)

    requires ValidStack(st)
    requires inorder(root)
      == smallerInorder(root, node.key) + [(node.key, node.value)] + inorder(node.right) + inorderStack(st)

    ensures ValidStack(SearchAndPush(st, node, k))
    ensures inorder(root) == smallerInorder(root, k) + inorderStack(SearchAndPush(st, node, k))
  {
    SubtreeChildren(node, root);
    if node.key == k {
      calc == {
        inorder(root);
        smallerInorder(root, node.key) + [(node.key, node.value)] + inorder(node.right) + inorderStack(st);
        smallerInorder(root, k) + [(node.key, node.value)] + inorder(node.right) + inorderStack(st);
        { Associativity2(); }
        smallerInorder(root, k) + ([(node.key, node.value)] + inorder(node.right) + inorderStack(st));
        smallerInorder(root, k) + inorderStack(st + [node]);
        smallerInorder(root, k) + inorderStack(SearchAndPush(st, node, k));
      }
    } else if node.key < k {
      calc == {
        inorder(root);
        smallerInorder(root, node.key) + [(node.key, node.value)] + inorder(node.right) + inorderStack(st);
        smallerInorder(root, node.key) + [(node.key, node.value)] + (inorder(node.right.left) + [(node.right.key, node.right.value)] + inorder(node.right.right)) + inorderStack(st);
        { Associativity1(); }
        smallerInorder(root, node.key) + [(node.key, node.value)] + inorder(node.right.left) + [(node.right.key, node.right.value)] + inorder(node.right.right) + inorderStack(st);
        { SmallerInorderRightInd(root, node); }
        smallerInorder(root, node.right.key) + [(node.right.key, node.right.value)] + inorder(node.right.right) + inorderStack(st);
      }
      SearchAndPushSpec(root, st, node.right, k);
    } else {
      assert k < node.key;
      calc == {
        inorder(root);
        smallerInorder(root, node.key) + [(node.key, node.value)] + inorder(node.right) + inorderStack(st);
        { Associativity2(); }
        smallerInorder(root, node.key) + ([(node.key, node.value)] + inorder(node.right) + inorderStack(st));
        { SmallerInorderLeftInd(root, node); }
        (smallerInorder(root, node.left.key) + [(node.left.key, node.left.value)] + inorder(node.left.right)) + ([(node.key, node.value)] + inorder(node.right) + inorderStack(st));
        smallerInorder(root, node.left.key) + [(node.left.key, node.left.value)] + inorder(node.left.right) + ([(node.key, node.value)] + inorder(node.right) + inorderStack(st));
        smallerInorder(root, node.left.key) + [(node.left.key, node.left.value)] + inorder(node.left.right) + inorderStack(st + [node]);
      }
      SearchAndPushSpec(root, st + [node], node.left, k);
    }
  }

  function SearchAndPushRoot(root: rbtree, k: K): seq<rbtree>
    requires SearchTree(root)
    requires k in keys(root)
  {
    SearchAndPush([], root, k)
  }

  lemma SearchAndPushRootSpec(root: rbtree, k: K)
    requires SearchTree(root)
    requires k in keys(root)

    ensures ValidStack(SearchAndPushRoot(root, k))
    ensures inorder(root) == smallerInorder(root, k) + inorderStack(SearchAndPushRoot(root, k))
  {
    SearchAndPushSpec(root, [], root, k);
  }
}
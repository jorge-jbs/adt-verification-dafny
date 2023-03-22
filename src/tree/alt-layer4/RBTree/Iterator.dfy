include "../../../../src/tree/alt-layer4/KeyValue.dfy"
include "../../../../src/tree/alt-layer4/RBTree/Base.dfy"

module RBTree.Iterator {
  import opened KeyValue
  import opened Base

  type index = seq<bool>

  predicate IsIndex(root: rbtree, node: rbtree, i: index)
  {
    root.Node? &&
    if i == [] then
      root == node
    else if i[0] == false then
      IsIndex(root.left, node, i[1..])
    else
      IsIndex(root.right, node, i[1..])
  }

  lemma IsIndexChildren(root: rbtree, node: rbtree, i: index)
    requires IsIndex(root, node, i)
    requires node.Node?
    ensures node.left.Node? ==> IsIndex(root, node.left, i + [false])
    ensures node.right.Node? ==> IsIndex(root, node.right, i + [true])
  {
    if node.left.Node? {
      if i == [] {
      } else if i[0] == false {
        IsIndexChildren(root.left, node, i[1..]);
        assert i[1..] + [false] == (i + [false])[1..];
        assert IsIndex(root.left, node.left, i[1..] + [false]);
        assert IsIndex(root.left, node.left, (i + [false])[1..]);
        assert IsIndex(root, node.left, i + [false]);
      } else {
        IsIndexChildren(root.right, node, i[1..]);
        assert IsIndex(root.right, node.left, i[1..] + [false]);
        assert i[1..] + [false] == (i + [false])[1..];
        assert IsIndex(root.right, node.left, (i + [false])[1..]);
        assert IsIndex(root, node.left, i + [false]);
      }
    }
    if node.right.Node? {
      if i == [] {
      } else if i[0] == false {
        IsIndexChildren(root.left, node, i[1..]);
        assert i[1..] + [true] == (i + [true])[1..];
        assert IsIndex(root.left, node.right, i[1..] + [true]);
        assert IsIndex(root.left, node.right, (i + [true])[1..]);
        assert IsIndex(root, node.right, i + [true]);
      } else {
        IsIndexChildren(root.right, node, i[1..]);
        assert IsIndex(root.right, node.right, i[1..] + [true]);
        assert i[1..] + [true] == (i + [true])[1..];
        assert IsIndex(root.right, node.right, (i + [true])[1..]);
        assert IsIndex(root, node.right, i + [true]);
      }
    }
  }

  predicate ValidIndex(root: rbtree, i: index)
  {
    root.Node? &&
    if i == [] then
      true
    else if i[0] == false then
      ValidIndex(root.left, i[1..])
    else
      ValidIndex(root.right, i[1..])
  }

  lemma ValidIndexOfIsIndex(root: rbtree, node: rbtree, i: index)
    requires IsIndex(root, node, i)
    ensures ValidIndex(root, i)
  {}

  /*
  predicate ValidIndex(root: rbtree, i: index)
  {
    exists n: rbtree :: IsIndex(root, n, i)
  }
  */

  function Get(root: rbtree, i: index): rbtree
    requires ValidIndex(root, i)
    ensures IsIndex(root, Get(root, i), i)
    ensures Get(root, i).Node?
  {
    if i == [] then
      root
    else if i[0] == false then
      Get(root.left, i[1..])
    else
      Get(root.right, i[1..])
  }

  lemma IndexLemmas(root: rbtree, node: rbtree, i: index)
    ensures IsIndex(root, node, i) <==>
      && ValidIndex(root, i)
      && Get(root, i) == node
  {
    if IsIndex(root, node, i) {
      ValidIndexOfIsIndex(root, node, i);
    }
  }

  function inorderIndexAcc(t: rbtree, acc: index): seq<index>
  {
    match t {
      case Empty => []
      case Node(l, k, v, r, c) =>
        inorderIndexAcc(l, acc + [false]) + [acc] + inorderIndexAcc(r, acc + [true])
    }
  }

  function inorderIndex(t: rbtree): seq<index>
  {
    inorderIndexAcc(t, [])
  }

  function DescendAndPush(st: seq<index>, node: rbtree, i: index): seq<index>
    decreases node
  {
    if node.Empty? then
      st
    else
      DescendAndPush(st + [i], node.left, i + [false])
  }

  predicate ValidStack(root: rbtree, st: seq<index>)
  {
    forall k | 0 <= k < |st| :: ValidIndex(root, st[k])
  }

  lemma ExtendStack(root: rbtree, st: seq<index>, node: rbtree, i: index)
    requires ValidStack(root, st)
    requires IsIndex(root, node, i)
    ensures ValidStack(root, st + [i])
  {
    var st' := st + [i];
    assert forall k | 0 <= k < |st| :: ValidIndex(root, st[k]);
    assert forall k | 0 <= k < |st| :: ValidIndex(root, st'[k]);
    ValidIndexOfIsIndex(root, node, i);
    assert ValidIndex(root, st'[|st|]);
  }

  function inorderStack(root: rbtree, st: seq<index>): seq<index>
    requires ValidStack(root, st)
  {
    if st == [] then
      []
    else
      var i := st[|st|-1];
      var node := Get(root, i);
      if node.Empty? then
        inorderStack(root, st[..|st|-1])
      else
        [i] + inorderIndexAcc(node.right, i + [true]) + inorderStack(root, st[..|st|-1])
  }

  lemma DescendAndPushSpec(root: rbtree, st: seq<index>, node: rbtree, i: index, traversed: seq<index>)
    decreases node

    requires ValidStack(root, st)
    requires node.Empty? || IsIndex(root, node, i)
    requires inorderIndex(root) == traversed + inorderIndexAcc(node, i) + inorderStack(root, st)

    ensures ValidStack(root, DescendAndPush(st, node, i))
    ensures inorderIndex(root) == traversed + inorderStack(root, DescendAndPush(st, node, i))
  {
    if node.Empty? {
    } else {
      assert ValidStack(root, st + [i]) by {
        ExtendStack(root, st, node, i);
      }
      assert node.left.Empty? || IsIndex(root, node.left, i + [false]) by {
        IsIndexChildren(root, node, i);
      }
      assert inorderIndex(root)
          == traversed
          + inorderIndexAcc(node.left, i + [false])
          + inorderStack(root, st + [i]) by {
        ghost var st' := st + [i];
        assert i == st'[|st'|-1];
        assert node == Get(root, i) by {
          IndexLemmas(root, node, i);
        }
        if node.Empty? {
        } else {
          calc == {
            inorderIndex(root);
            traversed + inorderIndexAcc(node, i) + inorderStack(root, st);
            traversed
              + inorderIndexAcc(node.left, i + [false])
              + [i]
              + inorderIndexAcc(node.right, i + [true])
              + inorderStack(root, st);
            traversed
              + inorderIndexAcc(node.left, i + [false])
              + [i]
              + inorderIndexAcc(node.right, i + [true])
              + inorderStack(root, st'[..|st'|-1]);
            traversed
              + inorderIndexAcc(node.left, i + [false])
              + inorderStack(root, st');
          }
        }
      }
      DescendAndPushSpec(root, st + [i], node.left, i + [false], traversed);
    }
  }

  function Next(root: rbtree, st: seq<index>): seq<index>
    requires st != []  // has next
    requires ValidStack(root, st)
  {
    var i := st[|st|-1];
    var node := Get(root, i);
    DescendAndPush(st[..|st|-1], node.right, i + [true])
  }

  lemma NextSpec(root: rbtree, st: seq<index>, traversed: seq<index>)
    requires st != []
    requires ValidStack(root, st)
    requires inorderIndex(root) == traversed + inorderStack(root, st)

    ensures ValidStack(root, Next(root, st))
    ensures inorderIndex(root) == traversed + [st[|st|-1]] + inorderStack(root, Next(root, st))
  {
    var i := st[|st|-1];
    var node := Get(root, i);
    IsIndexChildren(root, node, i);
    DescendAndPushSpec(root, st[..|st|-1], node.right, i + [true], traversed + [i]);
  }
}
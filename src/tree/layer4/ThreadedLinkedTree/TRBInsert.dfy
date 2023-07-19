include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/TRBInsert.dfy"
include "../../../../src/tree/layer4/TTree1.dfy"
include "../../../../src/tree/layer4/TTNode1.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.TRBInsert {
  import opened KeyValue
  import TRB = TRBTree.Base
  import TRBi = TRBTree.TRBInsert
  import opened T = Tree
  import opened TTNode
  import opened Color

  // 14"
  method {:verify false} FlipColors(node: TTNode, ghost sk: ttree<TTNode>)
    modifies node`color, node.left`color, node.right`color

    requires ValidRec(node, sk)
    requires node.left != null
    requires !node.isThreadLeft
    requires node.right != null
    requires !node.isThreadRight
    requires TreeModelRec(sk).left.Child?  /* redundant */
    requires TreeModelRec(sk).left.child.Node?  /* redundant */
    requires TreeModelRec(sk).right.Child?  /* redundant */
    requires TreeModelRec(sk).right.child.Node?  /* redundant */

    ensures ValidRec(node, sk)
    ensures TreeModelRec(sk) == TRBi.FlipColors(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
  {
    node.color := NegColor(node.color);
    node.left.color := NegColor(node.left.color);
    node.right.color := NegColor(node.right.color);
  }

  // 20"
  method {:verify false} RotateLeft(node: TTNode, ghost sk: ttree<TTNode>)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies node`color
    modifies node`isThreadRight
    modifies node`right
    modifies node.right`isThreadLeft
    modifies node.right`left
    modifies node.right`color

    requires ValidRec(node, sk)
    requires node.right != null
    requires !node.isThreadRight
    requires TreeModelRec(sk).right.Child?  /* redundant */
    requires TreeModelRec(sk).right.child.Node?  /* redundant */

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBi.RotateLeft(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    assert node.right.isThreadLeft <==> sk.right.child.left.Thread? by {
      assert ValidRec(node.right, sk.right.child);
      assert ValidRecP(node.right.left, sk.right.child.left, node.right.isThreadLeft);
    }
    assert sk.right.child.left.Thread? <==> TreeModelRec(sk).right.child.left.Thread? by {
      assert sk.right.child.left.Thread? <==> TreeModelRecP(sk.right.child.left).Thread?;
      assert sk.right.child.left.Thread? <==> TreeModelRec(sk.right.child).left.Thread?;
      assert sk.right.child.left.Thread? <==> TreeModelRecP(sk.right).child.left.Thread?;
      assert sk.right.child.left.Thread? <==> TreeModelRec(sk).right.child.left.Thread?;
    }
    newNode := node.right;
    ghost var newChildLeftRight;
    assert newNode.isThreadLeft <==> old(TreeModelRec(sk)).right.child.left.Thread?;
    if newNode.isThreadLeft {
      node.right := newNode;
      node.isThreadRight := true;
      newChildLeftRight := T.Thread(newNode);
      assert ValidRecP(node.right, newChildLeftRight, true);
      assert TreeModelRecP(newChildLeftRight) == RB.Thread(old(TreeModelRec(sk)).right.child.key);
    } else {
      node.right := newNode.left;
      node.isThreadRight := false;
      newChildLeftRight := sk.right.child.left;
      assert ValidRecP(node.right, newChildLeftRight, false);
      assert TreeModelRecP(newChildLeftRight) == old(TreeModelRec(sk)).right.child.left;
    }
    assert vlr: ValidRecP(node.right, newChildLeftRight, node.isThreadRight);
    assert TreeModelRecP(newChildLeftRight) == if old(TreeModelRec(sk)).right.child.left.Thread? then
          RB.Thread(old(TreeModelRec(sk)).right.child.key)
        else
          old(TreeModelRec(sk)).right.child.left;
    newNode.color := node.color;
    node.color := Red;
    newNode.left := node;
    newNode.isThreadLeft := false;
    newSk := T.Node(T.Child(T.Node(sk.left, node, newChildLeftRight)), newNode, sk.right.child.right);
    assert ValidRec(newNode, newSk) by {
      assert ValidRec(newNode.left, newSk.left.child) by {
        assert ValidRecP(newNode.left.left, sk.left, newNode.left.isThreadLeft) by {
          assert newNode.left.left == node.left;
          assert ValidRecP(node.left, sk.left, node.isThreadLeft);
        }
        assert ValidRecP(newNode.left.right, newChildLeftRight, newNode.left.isThreadRight) by {
          assert newNode.left.right == node.right;
          assert newNode.left.isThreadRight == node.isThreadRight;
          assert ValidRecP(node.right, newChildLeftRight, node.isThreadRight) by {
            reveal vlr;
          }
        }
      }
    }
  }

  // 15"
  method {:verify false} RotateRight(node: TTNode, ghost sk: ttree<TTNode>)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies node`color
    modifies node`isThreadLeft
    modifies node`left
    modifies node.left`isThreadRight
    modifies node.left`right
    modifies node.left`color

    requires ValidRec(node, sk)
    requires node.left != null
    requires !node.isThreadLeft
    requires TreeModelRec(sk).left.Child?  /* redundant */
    requires TreeModelRec(sk).left.child.Node?  /* redundant */

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBi.RotateRight(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    assert node.left.isThreadRight <==> sk.left.child.right.Thread? by {
      assert ValidRec(node.left, sk.left.child);
      assert ValidRecP(node.left.right, sk.left.child.right, node.left.isThreadRight);
    }
    assert sk.left.child.right.Thread? <==> TreeModelRec(sk).left.child.right.Thread? by {
      assert sk.left.child.right.Thread? <==> TreeModelRecP(sk.left.child.right).Thread?;
      assert sk.left.child.right.Thread? <==> TreeModelRec(sk.left.child).right.Thread?;
      assert sk.left.child.right.Thread? <==> TreeModelRecP(sk.left).child.right.Thread?;
      assert sk.left.child.right.Thread? <==> TreeModelRec(sk).left.child.right.Thread?;
    }
    newNode := node.left;
    ghost var newChildRightLeft;
    if newNode.isThreadRight {
      node.left := newNode;
      node.isThreadLeft := true;
      newChildRightLeft := T.Thread(newNode);
      assert ValidRecP(node.left, newChildRightLeft, true);
      assert TreeModelRecP(newChildRightLeft) == RB.Thread(old(TreeModelRec(sk)).left.child.key);
    } else {
      node.left := newNode.right;
      node.isThreadLeft := false;
      newChildRightLeft := sk.left.child.right;
      assert ValidRecP(node.left, newChildRightLeft, false);
      assert TreeModelRecP(newChildRightLeft) == old(TreeModelRec(sk)).left.child.right;
    }
    assert vrl: ValidRecP(node.left, newChildRightLeft, node.isThreadLeft);
    assert TreeModelRecP(newChildRightLeft) == if old(TreeModelRec(sk)).left.child.right.Thread? then
          RB.Thread(old(TreeModelRec(sk)).left.child.key)
        else
          old(TreeModelRec(sk)).left.child.right;
    newNode.right := node;
    newNode.isThreadRight := false;
    newNode.color := node.color;
    node.color := Red;
    newSk := T.Node(sk.left.child.left, newNode, T.Child(T.Node(newChildRightLeft, node, sk.right)));
    assert ValidRec(newNode, newSk) by {
      assert ValidRec(newNode.right, newSk.right.child) by {
        assert ValidRecP(newNode.right.left, newChildRightLeft, newNode.right.isThreadLeft) by {
          assume false;
          assert newNode.right.left == node.left;
          assert newNode.right.isThreadLeft == node.isThreadLeft;
          assert ValidRecP(node.left, newChildRightLeft, node.isThreadLeft) by {
            reveal vrl;
          }
        }
        assert ValidRecP(newNode.right.right, sk.right, newNode.right.isThreadRight) by {
          assert newNode.right.right == node.right;
          assert ValidRecP(node.right, sk.right, node.isThreadRight);
        }
      }
    }
  }

  // 4"
  method {:verify false} Restore(node: TTNode, ghost sk: ttree<TTNode>)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies set x | x in elems(sk) :: x`isThreadLeft
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`isThreadRight
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBi.Restore(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    ghost var t := TreeModelRec(sk);
    ghost var t' :=
      if TRB.isRedP(t.right) then
        TRBi.RotateLeft(t)
      else
        t;
    ghost var t'' :=
      if TRB.isRedP(t'.left) && TRB.isRedP(t'.left.child.left) then
        TRBi.RotateRight(t')
      else
        t';
    ghost var t''' :=
      if TRB.isRedP(t''.left) && TRB.isRedP(t''.right) then
        TRBi.FlipColors(t'')
      else
        t'';
    newNode := node;
    newSk := sk;

    if newNode.right != null && !newNode.isThreadRight && newNode.right.color.Red? {
      newNode, newSk := RotateLeft(newNode, newSk);
    }

    assert TreeModelRec(newSk) == t';

    isRedLeftProp(newNode, newSk);
    assert isRedLeft(newNode) <==> TRB.isRedP(t'.left);
    if newNode.left != null && !newNode.isThreadLeft {
      assert TreeModelRecP(newSk.left.child.left) == t'.left.child.left;
      isRedLeftProp(newNode.left, newSk.left.child);
      assert isRedLeft(newNode.left) <==> TRB.isRedP(t'.left.child.left);
    }
    if isRedLeft(newNode) && isRedLeft(newNode.left) {
      newNode, newSk := RotateRight(newNode, newSk);
      assert TreeModelRec(newSk) == TRBi.RotateRight(t');
    }

    assert TreeModelRec(newSk) == t'';

    if isRedLeft(newNode) && isRedRight(newNode) {
      FlipColors(newNode, newSk);
    }

    assert TreeModelRec(newSk) == t''';
  }

  method TRBInsertRecP(prev: TTNode?, node: TTNode?, isThread: bool, next: TTNode?, ghost sk: ttreePointer<TTNode>, k: K, v: V)
    returns (newNode: TTNode, newIsThread: bool, ghost newSk: ttreePointer<TTNode>, ghost insertedNode:TTNode)

    decreases sk

    modifies set x | x in elemsP(sk) :: x`isThreadLeft
    modifies set x | x in elemsP(sk) :: x`left
    modifies set x | x in elemsP(sk) :: x`isThreadRight
    modifies set x | x in elemsP(sk) :: x`right
    modifies set x | x in elemsP(sk) :: x`value
    modifies set x | x in elemsP(sk) :: x`color

    requires ValidRecP(node, sk, isThread)
    ensures ValidRecP(newNode, newSk, newIsThread)
    ensures
      TreeModelRecP(newSk)
        == TRBi.TRBInsertP(
            nodeToPointer(prev),
            old(TreeModelRecP(sk)),
            nodeToPointer(next),
            k,
            v
          )

    ensures elemsP(newSk) == elemsP(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v

    requires allocated(elemsP(sk))
    ensures fresh(elemsP(newSk)-elemsP(sk))
    ensures allocated(elemsP(newSk))
  {
    newIsThread := false;
    if !isThread {
      ghost var newChild;
      newNode, newChild, insertedNode := TRBInsertRec(prev, node, next, sk.child, k, v);
      newSk := T.Child(newChild);
    } else {
      ghost var newChildLeft :=
        if prev == null then
          T.Child(T.Empty)
        else
          T.Thread(prev as TTNode);
      ghost var newChildRight :=
        if next == null then
          T.Child(T.Empty)
        else
          T.Thread(next as TTNode);
      newNode := new TTNode(prev != null, prev, k, v, next != null, next, Red);
      newSk := T.Child(T.Node(newChildLeft, newNode, newChildRight));
      insertedNode := newNode;
      calc == {
        TreeModelRecP(newSk);
        TRB.Child(TRB.Node(TreeModelRecP(newChildLeft), newNode.key, newNode.value, TreeModelRecP(newChildRight), newNode.color));
        TRB.Child(TRB.Node(nodeToPointer(prev), k, v, nodeToPointer(next), Red));
        TRBi.TRBInsertP(
          nodeToPointer(prev),
          old(TreeModelRecP(sk)),
          nodeToPointer(next),
          k,
          v
        );
      }
    }
  }

  // 1'33"
  method {:verify false} TRBInsertRec(prev: TTNode?, node: TTNode?, next: TTNode?, ghost sk: ttree<TTNode>, k: K, v: V)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>, ghost insertedNode:TTNode)

    decreases sk

    modifies set x | x in elems(sk) :: x`isThreadLeft
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`isThreadRight
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`value
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)
    ensures ValidRec(newNode, newSk)
    ensures
      TreeModelRec(newSk)
        == TRBi.TRBInsert(
            nodeToPointer(prev),
            old(TreeModelRec(sk)),
            nodeToPointer(next),
            k,
            v
          )

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    if node == null {
      ghost var newChildLeft :=
        if prev != null then
          T.Thread(prev as TTNode)
        else
          T.Child(T.Empty);
      ghost var newChildRight :=
        if next != null then
          T.Thread(next as TTNode)
        else
          T.Child(T.Empty);
      newNode := new TTNode(prev != null, prev, k, v, next != null, next, Red);
      newSk := T.Node(newChildLeft, newNode, newChildRight);
      insertedNode := newNode;
    } else {
      assert sk.data == node;
      newNode := node;
      if k == node.key {
        node.value := v;
        newSk := sk;
        insertedNode := node;
      } else if node.key < k {
        ghost var newSkRight;
        node.right, node.isThreadRight, newSkRight, insertedNode := TRBInsertRecP(node, node.right, node.isThreadRight, next, sk.right, k, v);
        newSk := T.Node(sk.left, node, newSkRight);
        newNode, newSk := Restore(newNode, newSk);
      } else if k < node.key {
        ghost var newSkLeft;
        node.left, node.isThreadLeft, newSkLeft, insertedNode := TRBInsertRecP(prev, node.left, node.isThreadLeft, node, sk.left, k, v);
        newSk := T.Node(newSkLeft, node, sk.right);
        newNode, newSk := Restore(newNode, newSk);
      } else {
        assert false;
      }
    }
  }

  // 5"
  method TRBInsertRoot(node: TTNode?, ghost sk: ttree<TTNode>, k: K, v: V)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>, ghost insertedNode:TTNode)

    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`isThreadLeft
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`isThreadRight
    modifies set x | x in elems(sk) :: x`value
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)
    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBi.TRBInsertRoot(old(TreeModelRec(sk)), k, v)

    ensures elems(newSk) == elems(sk) + {insertedNode}
    ensures insertedNode.key == k && insertedNode.value == v

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode, newSk, insertedNode := TRBInsertRec(null, node, null, sk, k, v);
    newNode.color := Black;
  }
}

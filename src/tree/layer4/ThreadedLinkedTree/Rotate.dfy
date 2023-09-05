include "../../../../src/tree/layer4/TRBTree/Rotate.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.Rotate {
  import opened KeyValue
  import TRBr = TRBTree.Rotate
  import opened T = TTree
  import opened TTNode
  import opened Color

  method RotateLeft(node: TTNode, ghost sk: ttree<TTNode>)
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
    ensures TreeModelRec(newSk) == TRBr.RotateLeft(old(TreeModelRec(sk)))
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

  method RotateRight(node: TTNode, ghost sk: ttree<TTNode>)
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
    ensures TreeModelRec(newSk) == TRBr.RotateRight(old(TreeModelRec(sk)))
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
}

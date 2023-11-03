include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/ThreadedLinkedTree/FlipColors.dfy"
include "../../../../src/tree/layer4/ThreadedLinkedTree/Rotate.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/MoveRed.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.MoveRed {
  import opened Utils
  import opened KeyValue
  import TRB = TRBTree.Base
  import TRBf = TRBTree.FlipColors
  import TRBr = TRBTree.Rotate
  import TRBm = TRBTree.MoveRed
  import opened T = TTree
  import opened FC = FlipColors
  import opened R = Rotate
  import opened TTNode
  import opened Color

  // 15"
  method MoveRedLeft(
      node: TTNode, 
      ghost prev: threadOrEmpty<TTNode>, 
      ghost sk: ttree<TTNode>, 
      ghost next: threadOrEmpty<TTNode>
    )
      returns (newNode: TTNode, ghost newSk: ttree<TTNode>)
    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`isThreadLeft
    modifies set n | n in elems(sk) :: n`right
    modifies set n | n in elems(sk) :: n`isThreadRight

    requires ValidRec(node, sk)
    requires ThreadedNe(prev, sk, next)
    requires node.left != null
    requires !node.isThreadLeft
    requires node.right != null
    requires !node.isThreadRight
    requires TRBm.MoveRedLeft.requires(TreeModelRec(sk))

    ensures ValidRec(newNode, newSk)
    ensures ThreadedNe(prev, newSk, next)
    ensures elems(newSk) == elems(sk)
    ensures TreeModelRec(newSk) == TRBm.MoveRedLeft(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(newSk))
    ensures fresh(elems(newSk)-elems(sk))
  {
    newNode := node;
    newSk := sk;
    FlipColors(newNode, prev, newSk, next);
    if isRedLeft(newNode.right) {
      ghost var newSkRight;
      assert
        && {newNode.right, newNode.right.left} <= elems(newSk) == elems(sk)
        && {newNode, newNode.right, newNode.right.left} !! elems(newSk.left)
      by {
        assert ValidRec(newNode, newSk);
        assert ValidRec(newNode.right.left, newSk.right.left);
      }
      label PreRR:
      newNode.right, newSkRight := RotateRight(newNode.right, Thread(newNode), newSk.right, next);
      assert unchanged@PreRR(elems(newSk.left));
      newSk := Node(newSk.left, newNode, newSkRight);
      assert ValidRec(newNode, newSk) by {
        assert ValidRec(newNode.right, newSk.right);
        assert ValidRec(newNode.left, newSk.left);
        assert !newNode.isThreadRight;
      }
      newNode, newSk := RotateLeft(newNode, prev, newSk, next);
      FlipColors(newNode, prev, newSk, next);
    }
    assert TreeModelRec(newSk) == TRBm.MoveRedLeft(old(TreeModelRec(sk))) by {
      assume {:axiom} false;
    }
  }

  // 33"
  method MoveRedRight(
      node: TTNode, 
      ghost prev: threadOrEmpty<TTNode>, 
      ghost sk: ttree<TTNode>, 
      ghost next: threadOrEmpty<TTNode>
    )
      returns (newNode: TTNode, ghost newSk: ttree<TTNode>)
    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`isThreadRight
    modifies set n | n in elems(sk) :: n`right
    modifies set n | n in elems(sk) :: n`isThreadLeft

    requires ValidRec(node, sk)
    requires ThreadedNe(prev, sk, next)
    requires node.left != null
    requires !node.isThreadLeft
    requires node.right != null
    requires !node.isThreadRight
    requires TRBm.MoveRedRight.requires(TreeModelRec(sk))

    ensures ValidRec(newNode, newSk)
    ensures ThreadedNe(prev, newSk, next)
    ensures elems(newSk) == elems(sk)
    ensures TreeModelRec(newSk) == TRBm.MoveRedRight(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(newSk))
    ensures fresh(elems(newSk)-elems(sk))
  {
    newNode := node;
    newSk := sk;
    FlipColors(newNode, prev, newSk, next);
    isRedLeftProp(newNode.left, newSk.left);
    if isRedLeft(newNode.left) {
      newNode, newSk := RotateRight(newNode, prev, newSk, next);
      assert
        && newNode.right.right != null
        && !newNode.right.isThreadRight
        && TreeModelRec(newSk.right).right.Node?
        && {newNode.right, newNode.right.right} <= elems(newSk) == elems(sk)
        && {newNode, newNode.right, newNode.right.right} !! elems(newSk.left)
      by {
        assert TreeModelRec(newSk).right.right.Node?;
        assert TreeModelRec(newSk.right).right.Node?;
        assert TreeModelRec(newSk.right.right).Node?;
        assert ValidRec(newNode, newSk);
        assert ValidRec(newNode.right, newSk.right);
        assert ValidRec(newNode.right.right, newSk.right.right);
        assert ValidRec(newNode, newSk);
        assert ValidRec(newNode.right, newSk.right);
        assert elems(newSk.left) !! elems(newSk.right);
      }
      FlipColors(newNode, prev, newSk, next);
      label PreRL:
      ghost var newSkRight;
      newNode.right, newSkRight := RotateLeft(newNode.right, Thread(newNode), newSk.right, next);
      assert unchanged@PreRL(elems(newSk.left));
      newSk := Node(newSk.left, newNode, newSkRight);
      assert ValidRec(newNode, newSk) by {
        assert ValidRec(newNode.right, newSk.right);
        assert ValidRec(newNode.left, newSk.left);
      }
    }
    assert TreeModelRec(newSk) == TRBm.MoveRedRight(old(TreeModelRec(sk))) by {
      assume {:axiom} false;
    }
  }
}

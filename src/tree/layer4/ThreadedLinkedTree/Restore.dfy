include "../../../../src/tree/layer4/ThreadedLinkedTree/FlipColors.dfy"
include "../../../../src/tree/layer4/ThreadedLinkedTree/Rotate.dfy"
include "../../../../src/tree/layer4/TRBTree/Restore.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.Restore {
  import opened KeyValue
  import opened FC = FlipColors
  import opened Rotate
  import TRB = TRBTree.Base
  import TRBr = TRBTree.Rotate
  import TRBres = TRBTree.Restore
  import opened T = TTree
  import opened TTNode
  import opened Color

  method Restore(
      node: TTNode, 
      ghost prev: threadOrEmpty<TTNode>,
      ghost sk: ttree<TTNode>,
      ghost next: threadOrEmpty<TTNode>
    )
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies set x | x in elems(sk) :: x`isThreadLeft
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`isThreadRight
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)
    requires ThreadedNe(prev, sk, next)

    ensures ValidRec(newNode, newSk)
    ensures ThreadedNe(prev, newSk, next)
    ensures TreeModelRec(newSk) == TRBres.Restore(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode := node;
    newSk := sk;

    if newNode.right != null && !newNode.isThreadRight && newNode.right.color.Red? {
      newNode, newSk := RotateLeft(newNode, prev, newSk, next);
    }

    if isRedLeft(newNode) && isRedLeft(newNode.left) {
      newNode, newSk := RotateRight(newNode, prev, newSk, next);
    }

    if isRedLeft(newNode) && isRedRight(newNode) {
      FlipColors(newNode, prev, newSk, next);
    }

    assert TreeModelRec(newSk) == TRBres.Restore(old(TreeModelRec(sk))) by {
      assume false;
    }
  }
}

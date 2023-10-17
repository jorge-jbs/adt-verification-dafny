include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/AltThreadedLinkedTree/Restore.dfy"
include "../../../../src/tree/layer4/AltThreadedLinkedTree/MoveRed.dfy"
include "../../../../src/tree/layer4/AltTRBTree/Base.dfy"
include "../../../../src/tree/layer4/AltTRBTree/MoveRed.dfy"
include "../../../../src/tree/layer4/AltTRBTree/RemoveMinMaintainingPrev.dfy"
include "../../../../src/tree/layer4/AltTTree.dfy"
include "../../../../src/tree/layer4/AltTTNode2.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.RemoveMinMaintainingPrev {
  import opened Utils
  import opened KeyValue
  import TRB = TRBTree.Base
  import TRBf = TRBTree.FlipColors
  import TRBr = TRBTree.Rotate
  import TRBres = TRBTree.Restore
  import TRBm = TRBTree.MoveRed
  import TRBrm = TRBTree.RemoveMinMaintainingPrev
  import opened T = TTree
  import opened MoveRed
  import opened R = Restore
  import opened TTNode
  import opened Color

  method RemoveMinMaintainingPrev(  // 1'28"
      node: TTNode,
      ghost prev: threadOrEmpty<TTNode>,
      ghost sk: ttree<TTNode>, 
      ghost next: threadOrEmpty<TTNode>,
      isLeft: bool
    )
      returns (
        newNode: TTNode?, 
        ghost newSk: ttreeOrThread<TTNode>, 
        isThreadNewNode: bool, 
        minNode: TTNode
      )
    decreases TRB.size(TreeModelRec(sk))

    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`isThreadLeft
    modifies set n | n in elems(sk) :: n`right
    modifies set n | n in elems(sk) :: n`isThreadRight

    requires ValidRec(node, sk)
    requires ThreadedNe(prev, sk, next)
    requires TRBrm.RemoveMinMaintainingPrev(TreeModelRec(sk), isLeft).Some?

    ensures ValidChild(newNode, newSk, isThreadNewNode)
    ensures ThreadedRecCond(nodeToThread(minNode), newSk, next, isLeft)
    ensures minNode in elems(sk)
    ensures elems(newSk) == elems(sk) - {minNode}
    ensures TreeModelRec(newSk) == TRBrm.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.0
    ensures minNode.key == TRBrm.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.1
    ensures minNode.value == TRBrm.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.2

    requires allocated(elems(sk))
    ensures allocated(elems(newSk))
    ensures fresh(elems(newSk)-elems(sk))
  {
    newNode := node;
    newSk := sk;
    ghost var t := TreeModelRec(newSk);
    if newNode.isThreadLeft || newNode.left == null {
      assert newNode.isThreadRight || newNode.right == null;
      if isLeft {
        newNode := newNode;
        newSk := Thread(newNode);
        isThreadNewNode := true;
        minNode := newNode;
      } else {
        isThreadNewNode := newNode.isThreadRight;
        minNode := newNode;
        newNode := newNode.right;
        newSk := newSk.right;
      }
    } else {
      isBlackLeftProp(newNode, newSk);
      if isBlackLeft(newNode) {
        isRedLeftProp(newNode.left, newSk.left);
      }
      if isBlackLeft(newNode) && !isRedLeft(newNode.left) {
        newNode, newSk := MoveRedLeft(newNode, prev, newSk, next);
        TRBm.MoveRedLeftSize(t);
      } else {
        newNode, newSk := newNode, newSk;
      }
      ghost var t' := TreeModelRec(newSk);
      assert ThreadedNe(prev, newSk, next);
      assert ThreadedRecL(prev, newSk.left, Thread(newSk.data));
      label PreRec:
      ghost var newSkLeft;
      newNode.left, newSkLeft, newNode.isThreadLeft, minNode := RemoveMinMaintainingPrev(
        newNode.left, 
        prev,
        newSk.left, 
        Thread(newNode),
        true
      );
      assert unchanged@PreRec(elems(newSk.right));
      newSk := Node(newSkLeft, newNode, newSk.right);
      ghost var t'' := TreeModelRec(newSk);
      assert ValidRec(newNode, newSk) by {
        //assume false;
        assert ValidChild(newNode.right, newSk.right, newNode.isThreadRight) by {
          assert unchanged@PreRec(elems(newSk.right));
        }
        assert ValidChild(newNode.left, newSk.left, newNode.isThreadLeft);
      }
      assert ThreadedNe(nodeToThread(minNode), newSk, next);
      newNode, newSk := Restore(newNode, nodeToThread(minNode), newSk, next);
      isThreadNewNode := false;
      ghost var t''' := TreeModelRec(newSk);
      assert
        && TreeModelRec(newSk) == TRBrm.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.0
        && minNode.key == TRBrm.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.1
        && minNode.value == TRBrm.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.2
      by {
        calc == {
          TreeModelRec(newSk);
          t''';
          TRBres.Restore(t'');
          //{ assume false; }
          TRBres.Restore(TRB.Node(TRBrm.RemoveMinMaintainingPrev(t'.left, true).unwrap.0, t'.key, t'.value, t'.right, t'.color));
          //{ assume false; }
          TRBrm.RemoveMinMaintainingPrev(t, isLeft).unwrap.0;
          TRBrm.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.0;
        }
        assert minNode.key == TRBrm.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.1 by {
          //assume false;
        }
        assert minNode.value == TRBrm.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.2 by {
          //assume false;
        }
      }
      assert ValidChild(newNode, newSk, isThreadNewNode) by {  // 60"
        //assume false;
      }
      assert ThreadedRecCond(nodeToThread(minNode), newSk, next, isLeft) by {
        //assume false;
      }
      assert minNode in elems(sk) by {
        //assume false;
      }
      assert elems(newSk) == elems(sk) - {minNode} by {  // 37"
        //assume false;
      }
      //assume false;
    }
  }
}

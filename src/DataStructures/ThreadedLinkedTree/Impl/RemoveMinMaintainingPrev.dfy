include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/Restore.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/MoveRed.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTree.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTNode.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/MoveRed.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/RemoveMinMaintainingPrev.dfy"

module ThreadedLinkedTree.Impl.RemoveMinMaintainingPrev {
  import opened KeyValue
  import opened Model.Color
  import ModelB = Model.Base
  import ModelF = Model.FlipColors
  import ModelRes = Model.Restore
  import ModelM = Model.MoveRed
  import ModelRM = Model.RemoveMinMaintainingPrev
  import opened T = TTree
  import opened MoveRed
  import opened R = Restore
  import opened TTNode

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
    decreases ModelB.size(TreeModelRec(sk))

    modifies set n | n in elems(sk) :: n`color
    modifies set n | n in elems(sk) :: n`left
    modifies set n | n in elems(sk) :: n`isThreadLeft
    modifies set n | n in elems(sk) :: n`right
    modifies set n | n in elems(sk) :: n`isThreadRight

    requires ValidRec(node, sk)
    requires ThreadedNe(prev, sk, next)
    requires ModelRM.RemoveMinMaintainingPrev(TreeModelRec(sk), isLeft).Some?

    ensures ValidChild(newNode, newSk, isThreadNewNode)
    ensures ThreadedRecCond(nodeToThread(minNode), newSk, next, isLeft)
    ensures minNode in elems(sk)
    ensures elems(newSk) == elems(sk) - {minNode}
    ensures TreeModelRec(newSk) == ModelRM.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.0
    ensures minNode.key == ModelRM.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.1
    ensures minNode.value == ModelRM.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.2

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
        ModelM.MoveRedLeftSize(t);
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
        && TreeModelRec(newSk) == ModelRM.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.0
        && minNode.key == ModelRM.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.1
        && minNode.value == ModelRM.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.2
      by {
        calc == {
          TreeModelRec(newSk);
          t''';
          ModelRes.Restore(t'');
          //{ assume false; }
          ModelRes.Restore(ModelB.Node(ModelRM.RemoveMinMaintainingPrev(t'.left, true).unwrap.0, t'.key, t'.value, t'.right, t'.color));
          //{ assume false; }
          ModelRM.RemoveMinMaintainingPrev(t, isLeft).unwrap.0;
          ModelRM.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.0;
        }
        assert minNode.key == ModelRM.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.1 by {
          //assume false;
        }
        assert minNode.value == ModelRM.RemoveMinMaintainingPrev(old(TreeModelRec(sk)), isLeft).unwrap.2 by {
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

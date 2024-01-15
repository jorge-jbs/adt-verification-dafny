include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Restore.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/FlipColors.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/Rotate.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTree.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTNode.dfy"

module ThreadedLinkedTree.Impl.Restore {
  import opened KeyValue
  import opened FC = FlipColors
  import opened Rotate
  import opened Model.Color
  import Model = Model.Restore
  import opened T = TTree
  import opened TTNode

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
    ensures TreeModelRec(newSk) == Model.Restore(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode := node;
    newSk := sk;

    isRedRightProp(newNode, newSk);
    if isRedRight(newNode) {
      newNode, newSk := RotateLeft(newNode, prev, newSk, next);
    }

    isRedLeftProp(newNode, newSk);
    if isRedLeft(newNode) {
      isRedLeftProp(newNode.left, newSk.left);
    }
    if isRedLeft(newNode) && isRedLeft(newNode.left) {
      newNode, newSk := RotateRight(newNode, prev, newSk, next);
    }

    isRedLeftProp(newNode, newSk);
    isRedRightProp(newNode, newSk);
    if isRedLeft(newNode) && isRedRight(newNode) {
      FlipColors(newNode, prev, newSk, next);
    }
  }
}

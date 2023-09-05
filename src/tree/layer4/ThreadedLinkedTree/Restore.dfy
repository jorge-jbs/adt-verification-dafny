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

  // 4"
  method Restore(node: TTNode, ghost sk: ttree<TTNode>)
    returns (newNode: TTNode, ghost newSk: ttree<TTNode>)

    modifies set x | x in elems(sk) :: x`isThreadLeft
    modifies set x | x in elems(sk) :: x`left
    modifies set x | x in elems(sk) :: x`isThreadRight
    modifies set x | x in elems(sk) :: x`right
    modifies set x | x in elems(sk) :: x`color

    requires ValidRec(node, sk)

    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk) == TRBres.Restore(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    ghost var t := TreeModelRec(sk);
    ghost var t' :=
      if TRB.isRedP(t.right) then
        TRBr.RotateLeft(t)
      else
        t;
    ghost var t'' :=
      if TRB.isRedP(t'.left) && TRB.isRedP(t'.left.child.left) then
        TRBr.RotateRight(t')
      else
        t';
    ghost var t''' :=
      if TRB.isRedP(t''.left) && TRB.isRedP(t''.right) then
        TRBf.FlipColors(t'')
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
      assert TreeModelRec(newSk) == TRBr.RotateRight(t');
    }

    assert TreeModelRec(newSk) == t'';

    if isRedLeft(newNode) && isRedRight(newNode) {
      FlipColors(newNode, newSk);
    }

    assert TreeModelRec(newSk) == t''';
  }
}

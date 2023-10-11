include "../../../../src/tree/layer4/ThreadedLinkedTree/FlipColors.dfy"
include "../../../../src/tree/layer4/ThreadedLinkedTree/Rotate.dfy"
include "../../../../src/tree/layer4/ThreadedLinkedTree/Restore.dfy"
include "../../../../src/tree/layer4/TRBTree/Restore.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.OpRestore {
  import opened KeyValue
  import opened FC = FlipColors
  import opened Rotate
  import opened Res = Restore
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

    requires OpValidRec(node, sk)

    ensures OpValidRec(newNode, newSk)
    ensures reveal OpValidRec(); true
    ensures TreeModelRec(newSk) == TRBres.Restore(old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    OpValidEq(node, sk);
    newNode, newSk := Res.Restore(node, sk);
    OpValidEq(newNode, newSk);
  }
}

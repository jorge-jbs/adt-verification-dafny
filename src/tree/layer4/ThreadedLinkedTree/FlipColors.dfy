include "../../../../src/tree/layer4/TRBTree/FlipColors.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.FlipColors {
  import opened KeyValue
  import TRBf = TRBTree.FlipColors
  import opened T = TTree
  import opened TTNode
  import opened Color

  // 14"
  method FlipColors(node: TTNode, ghost sk: ttree<TTNode>)
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
    ensures TreeModelRec(sk) == TRBf.FlipColors(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
  {
    node.color := NegColor(node.color);
    node.left.color := NegColor(node.left.color);
    node.right.color := NegColor(node.right.color);
  }
}

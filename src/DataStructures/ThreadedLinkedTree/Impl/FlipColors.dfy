include "../../../../src/DataStructures/ThreadedLinkedTree/Model/FlipColors.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTree.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTNode.dfy"

module ThreadedLinkedTree.Impl.FlipColors {
  import opened KeyValue
  import opened Model.Color
  import Model = Model.FlipColors
  import opened T = TTree
  import opened TTNode

  method FlipColors(
      node: TTNode,
      ghost prev: threadOrEmpty<TTNode>,
      ghost sk: ttree<TTNode>,
      ghost next: threadOrEmpty<TTNode>
    )
    modifies node`color, node.left`color, node.right`color

    requires ValidRec(node, sk)
    requires ThreadedNe(prev, sk, next)
    requires node.left != null
    requires !node.isThreadLeft
    requires node.right != null
    requires !node.isThreadRight
    requires TreeModelRec(sk).left.Node?  /* redundant */
    requires TreeModelRec(sk).right.Node?  /* redundant */

    ensures ValidRec(node, sk)
    ensures ThreadedNe(prev, sk, next)
    ensures TreeModelRec(sk) == Model.FlipColors(old(TreeModelRec(sk)))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
  {
    node.color := NegColor(node.color);
    node.left.color := NegColor(node.left.color);
    node.right.color := NegColor(node.right.color);
  }
}

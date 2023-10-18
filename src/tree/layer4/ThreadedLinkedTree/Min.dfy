include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/TRBInsert.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"

module ThreadedLinkedTree.Min {
  import opened KeyValue
  import TRB = TRBTree.Base
  import TRBi = TRBTree.TRBInsert
  import opened T = TTree
  import opened TTNode

  method Min(node: TTNode, ghost sk: nettree<TTNode>)
      returns (minNode: TTNode, ghost minSk: ttree<TTNode>)
    requires ValidRec(node, sk)
    ensures ValidRec(minNode, minSk)
    ensures minNode in elems(sk)
    ensures T.Subtree(minSk, sk)
    ensures TreeModelRec(minSk) == TRB.minSubtree(TreeModelRec(sk))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
    ensures allocated(elems(minSk))
  {
    if node.left != null && !node.isThreadLeft {
      minNode, minSk := Min(node.left, sk.left);
    } else {
      minNode, minSk := node, sk;
    }
  }
}

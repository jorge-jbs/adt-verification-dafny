include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/TRBInsert.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"

module ThreadedLinkedTree.Max {
  import opened KeyValue
  import TRB = TRBTree.Base
  import TRBi = TRBTree.TRBInsert
  import opened T = TTree
  import opened TTNode

  method Max(node: TTNode, ghost sk: nettree<TTNode>)
      returns (maxNode: TTNode, ghost maxSk: ttree<TTNode>)
    requires ValidRec(node, sk)
    ensures ValidRec(maxNode, maxSk)
    ensures maxNode in elems(sk)
    ensures T.Subtree(maxSk, sk)
    ensures TreeModelRec(maxSk) == TRB.maxSubtree(TreeModelRec(sk))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
    ensures allocated(elems(maxSk))
  {
    if node.right != null && !node.isThreadRight {
      maxNode, maxSk := Max(node.right, sk.right);
    } else {
      maxNode, maxSk := node, sk;
    }
  }
}

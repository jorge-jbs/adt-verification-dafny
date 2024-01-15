include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTree.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTNode.dfy"

module ThreadedLinkedTree.Impl.Max {
  import Model = Model.Base
  import opened T = TTree
  import opened TTNode

  method Max(node: TTNode, ghost sk: nettree<TTNode>)
      returns (maxNode: TTNode, ghost maxSk: ttree<TTNode>)
    requires ValidRec(node, sk)
    ensures ValidRec(maxNode, maxSk)
    ensures maxNode in elems(sk)
    ensures T.Subtree(maxSk, sk)
    ensures TreeModelRec(maxSk) == Model.maxSubtree(TreeModelRec(sk))

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

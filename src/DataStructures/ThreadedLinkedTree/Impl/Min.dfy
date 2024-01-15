include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTree.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTNode.dfy"

module ThreadedLinkedTree.Impl.Min {
  import Model = Model.Base
  import opened T = TTree
  import opened TTNode

  method Min(node: TTNode, ghost sk: nettree<TTNode>)
      returns (minNode: TTNode, ghost minSk: ttree<TTNode>)
    requires ValidRec(node, sk)
    ensures ValidRec(minNode, minSk)
    ensures minNode in elems(sk)
    ensures T.Subtree(minSk, sk)
    ensures TreeModelRec(minSk) == Model.minSubtree(TreeModelRec(sk))

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

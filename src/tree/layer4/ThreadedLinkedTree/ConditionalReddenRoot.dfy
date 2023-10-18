include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.ConditionalReddenRoot {
  import opened KeyValue
  import TRB = TRBTree.Base
  import opened T = TTree
  import opened TTNode
  import opened Color

  method ConditionalReddenRoot(node: TTNode?, ghost sk: ttree<TTNode>)
    modifies node

    requires ValidRec(node, sk)
    requires ThreadedRoot(sk)

    ensures ValidRec(node, sk)
    requires ThreadedRoot(sk)
    ensures TreeModelRec(sk) == TRB.ConditionalReddenRoot(old(TreeModelRec(sk)))
  {
    if node != null && !isRedLeft(node) {
      node.color := Red;
    }
  }
}
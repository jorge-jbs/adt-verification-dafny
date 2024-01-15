include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTree.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTNode.dfy"

module ThreadedLinkedTree.Impl.ConditionalReddenRoot {
  import opened KeyValue
  import opened Model.Color
  import Model = Model.Base
  import opened T = TTree
  import opened TTNode

  method ConditionalReddenRoot(node: TTNode?, ghost sk: ttree<TTNode>)
    modifies node

    requires ValidRec(node, sk)
    requires ThreadedRoot(sk)

    ensures ValidRec(node, sk)
    requires ThreadedRoot(sk)
    ensures TreeModelRec(sk) == Model.ConditionalReddenRoot(old(TreeModelRec(sk)))
  {
    if node != null && !isRedLeft(node) {
      node.color := Red;
    }
  }
}
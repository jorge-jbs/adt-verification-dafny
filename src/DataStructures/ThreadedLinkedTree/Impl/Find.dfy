include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Find.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTree.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTNode.dfy"

module ThreadedLinkedTree.Impl.Find {
  import opened KeyValue
  import Model = Model.Find
  import opened T = TTree
  import opened TTNode

  method FindRec(
    node: TTNode?,
    isThread: bool,
    ghost sk: ttreeOrThread<TTNode>,
    k: K
  )
    returns (
      foundNode: TTNode?,
      ghost foundSk: ttree<TTNode>
    )
    decreases sk

    requires ValidChild(node, sk, isThread)

    ensures ValidChild(foundNode, foundSk, false)
    ensures foundNode != null ==> foundNode in elems(sk)

    ensures foundNode == null <==> Model.Find(TreeModelRec(sk), k).Null?
    ensures foundNode != null ==> Model.Find(TreeModelRec(sk), k).link == foundNode.key == k
  {
    if node == null || isThread {
      foundNode := null;
      foundSk := Empty;
    } else if node.key == k {
      foundNode := node;
      foundSk := sk;
    } else if k < node.key {
      foundNode, foundSk := FindRec(node.left, node.isThreadLeft, sk.left, k);
    } else {
      foundNode, foundSk := FindRec(node.right, node.isThreadRight, sk.right, k);
    }
  }
}

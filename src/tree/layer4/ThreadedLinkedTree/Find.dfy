include "../../../../src/tree/layer4/TRBTree/Iterator.dfy"
include "../../../../src/tree/layer4/TRBTree/Find.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.Find {
  import opened KeyValue
  import TRB = TRBTree.Find
  import TRBit = TRBTree.Iterator
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

    ensures foundNode != null <==> TRB.Find(TreeModelRec(sk), k).Link?
    ensures foundNode == null <==> TRB.Find(TreeModelRec(sk), k).PastTheEnd?
    ensures foundNode != null ==> TRB.Find(TreeModelRec(sk), k).link == foundNode.key == k
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

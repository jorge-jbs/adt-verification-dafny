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

  method MinP(node: TTNode, ghost sk: ttreePointer<TTNode>)
      returns (newNode: TTNode, ghost newSk: ttree<TTNode>)
    requires ValidRecP(node, sk, false)
    ensures ValidRec(newNode, newSk)
    ensures TreeModelRec(newSk)
      == TRB.minSubtreeP(TreeModelRecP(sk))
    ensures newNode in elemsP(sk)
    ensures T.SubtreeP(newSk, sk)
    ensures TRB.SubtreeP(TreeModelRec(newSk), TreeModelRecP(sk))

    requires allocated(elemsP(sk))
    ensures allocated(elemsP(sk))
    ensures allocated(elems(newSk))
  {
    newNode, newSk := Min(node, sk.child);
  }

  method Min(node: TTNode, ghost sk: ttree<TTNode>)
      returns (newNode: TTNode, ghost newSk: ttree<TTNode>)
    requires ValidRec(node, sk)
    ensures ValidRec(newNode, newSk)
    ensures newNode in elems(sk)
    ensures T.Subtree(newSk, sk)
    ensures TreeModelRec(newSk)
      == TRB.minSubtree(TreeModelRec(sk))

    requires allocated(elems(sk))
    ensures allocated(elems(sk))
    ensures allocated(elems(newSk))
  {
    if node.left != null && !node.isThreadLeft {
      newNode, newSk := MinP(node.left, sk.left);
    } else {
      newNode, newSk := node, sk;
    }
  }
}

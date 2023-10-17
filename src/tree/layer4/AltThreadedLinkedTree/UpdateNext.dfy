include "../../../../src/tree/layer4/AltTRBTree/Base.dfy"
include "../../../../src/tree/layer4/AltTRBTree/UpdateNext.dfy"
include "../../../../src/tree/layer4/AltTTree.dfy"
include "../../../../src/tree/layer4/AltTTNode2.dfy"

module ThreadedLinkedTree.UpdateNext {
  import TRB = TRBTree.Base
  import TRBun = TRBTree.UpdateNext
  import opened T = TTree
  import opened TTNode

  method UpdateNext(
      node: TTNode?,
      ghost prev: threadOrEmpty<TTNode>,
      ghost sk: ttree<TTNode>, 
      ghost next: threadOrEmpty<TTNode>,
      newNext: TTNode?
    )
      returns (ghost newSk: ttree<TTNode>)
    decreases sk

    modifies set n | n in elems(sk) :: n`right
    modifies set n | n in elems(sk) :: n`isThreadRight

    requires ValidRec(node, sk)
    requires sk.Node? ==> ThreadedNe(prev, sk, next)

    ensures ValidRec(node, newSk)
    ensures newSk.Node? ==> ThreadedNe(prev, newSk, nodeToThread(newNext))
    ensures TreeModelRec(newSk) == TRBun.UpdateNext(TreeModelRec(nodeToThread(newNext)), old(TreeModelRec(sk)))
    ensures elems(newSk) == elems(sk)

    requires allocated(elems(sk))
    ensures allocated(elems(newSk))
  {
    if node == null {
      newSk := sk;
    } else if node.right == null || node.isThreadRight {
      node.isThreadRight := newNext != null;
      node.right := newNext;
      newSk := sk.(right := nodeToThread(newNext));
    } else {
      ghost var newSkRight := UpdateNext(node.right, Thread(node), sk.right, next, newNext);
      newSk := sk.(right := newSkRight);
    }
  }
}

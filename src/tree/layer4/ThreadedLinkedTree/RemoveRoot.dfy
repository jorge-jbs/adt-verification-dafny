include "../../../../src/MUtils.dfy"
include "../../../../src/tree/layer4/ThreadedLinkedTree/Remove.dfy"
include "../../../../src/tree/layer4/ThreadedLinkedTree/BlackenRoot.dfy"
include "../../../../src/tree/layer4/ThreadedLinkedTree/ConditionalReddenRoot.dfy"
include "../../../../src/tree/layer4/TRBTree/Base.dfy"
include "../../../../src/tree/layer4/TRBTree/RemoveRoot.dfy"
include "../../../../src/tree/layer4/TTree.dfy"
include "../../../../src/tree/layer4/TTNode.dfy"
include "../../../../src/tree/layer4/Color.dfy"

module ThreadedLinkedTree.RemoveRoot {
  import opened Utils
  import opened Utils.Option
  import opened KeyValue
  import TRB = TRBTree.Base
  import TRBr = TRBTree.RemoveRoot
  import opened T = TTree
  import opened R = Remove
  import opened BR = BlackenRoot
  import opened CRR = ConditionalReddenRoot
  import opened TTNode
  import opened Color

  method RemoveRoot(node: TTNode?, ghost sk: ttree<TTNode>, k: K)
    returns (
      newNode: TTNode?,
      ghost newSk: ttree<TTNode>,
      ghost removedNode: TTNode?,
      isRemoved: bool
    )
    decreases TRB.size(TreeModelRec(sk))
    modifies elems(sk)

    requires ValidRec(node, sk)
    requires ThreadedRoot(sk)
    requires TRBr.RemoveRoot.requires(TreeModelRec(sk), k)
    requires TRBr.RemoveRoot(TreeModelRec(sk), k).Some?

    ensures ValidRec(newNode, newSk)
    ensures ThreadedRoot(newSk)
    ensures TreeModelRec(newSk) == TRBr.RemoveRoot(old(TreeModelRec(sk)), k).unwrap
    ensures isRemoved <==> TRBr.IsRemovedRoot(old(TreeModelRec(sk)), k)
    ensures isRemoved <==> removedNode != null
    ensures elems(newSk) == elems(sk) - {removedNode}
    ensures isRemoved ==> removedNode.key == k && removedNode in elems(sk)

    requires allocated(elems(sk))
    ensures fresh(elems(newSk)-elems(sk))
    ensures allocated(elems(newSk))
  {
    newNode := node;
    newSk := sk;
    CRR.ConditionalReddenRoot(newNode, newSk);
    var isThreadNewNode;
    newNode, isThreadNewNode, newSk, removedNode, isRemoved := R.Remove(newNode, false, Empty, newSk, Empty, false, k);
    {
      // Por qué funciona? podrían devolverme una hebra y newSk no sería del tipo ttree
      assert !isThreadNewNode;
      assert !newSk.Thread?;
      assert newSk is ttree<TTNode>;

      // Esto es por que en todo caso me devolverían null (Empty), nunca una hebra a un nodo real.
    }
    BR.BlackenRoot(newNode, newSk);
  }
}
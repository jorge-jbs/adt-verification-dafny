include "../../../../src/Collections/Option.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTree.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/TTNode.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/Remove.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/BlackenRoot.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Impl/ConditionalReddenRoot.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Color.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/Base.dfy"
include "../../../../src/DataStructures/ThreadedLinkedTree/Model/RemoveRoot.dfy"

module ThreadedLinkedTree.Impl.RemoveRoot {
  import opened Option
  import opened KeyValue
  import opened Model.Color
  import ModelB = Model.Base
  import ModelR = Model.RemoveRoot
  import opened T = TTree
  import opened R = Remove
  import opened BR = BlackenRoot
  import opened CRR = ConditionalReddenRoot
  import opened TTNode

  method RemoveRoot(node: TTNode?, ghost sk: ttree<TTNode>, k: K)
    returns (
      newNode: TTNode?,
      ghost newSk: ttree<TTNode>,
      ghost removedNode: TTNode?,
      isRemoved: bool
    )
    decreases Model.size(TreeModelRec(sk))
    modifies elems(sk)

    requires ValidRec(node, sk)
    requires ThreadedRoot(sk)
    requires ModelR.RemoveRoot.requires(TreeModelRec(sk), k)
    requires ModelR.RemoveRoot(TreeModelRec(sk), k).Some?

    ensures ValidRec(newNode, newSk)
    ensures ThreadedRoot(newSk)
    ensures TreeModelRec(newSk) == ModelR.RemoveRoot(old(TreeModelRec(sk)), k).unwrap
    ensures isRemoved <==> ModelR.IsRemovedRoot(old(TreeModelRec(sk)), k)
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